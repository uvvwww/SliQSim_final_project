#!/usr/bin/env python3
# filepath: /home/poshen/Desktop/schoolwork/QDA/SliQSim_final_project/test_gates.py

import subprocess
import json
import numpy as np
import os
import tempfile
import cmath
from itertools import product

SLIQSIM_PATH = "./SliQSim"
EXAMPLES_DIR = "./examples"
TEMP_DIR = "./temp_tests"

def ensure_temp_dir():
    """Create temporary directory if it doesn't exist."""
    if not os.path.exists(TEMP_DIR):
        os.makedirs(TEMP_DIR)

def basis_state_to_binary(state, num_qubits):
    """Convert an integer to its binary representation as a string."""
    return format(state, f'0{num_qubits}b')[::-1]

def create_test_qasm(filename, basis_state, num_qubits, gate_type, params=None):
    """Create a QASM file initializing to a specific basis state and applying the gate."""
    with open(filename, 'w') as f:
        f.write("OPENQASM 2.0;\n")
        f.write("include \"qelib1.inc\";\n\n")
        f.write(f"qreg q[{num_qubits}];\n")
        f.write(f"creg c[{num_qubits}];\n\n")
        
        # Initialize to specific basis state
        for i, bit in enumerate(basis_state):
            if bit == '1':
                f.write(f"x q[{i}];\n")
        
        f.write("\n")
        
        # Apply the gate
        if gate_type == "cp":
            angle = params.get("angle", "pi/4")
            control = params.get("control", 0)
            target = params.get("target", 1)
            f.write(f"cp({angle}) q[{control}], q[{target}];\n")
        elif gate_type == "maj":
            c1 = params.get("c1", 0)
            c2 = params.get("c2", 1)
            c3 = params.get("c3", 2) 
            target = params.get("target", 3)
            f.write(f"maj q[{c1}], q[{c2}], q[{c3}], q[{target}];\n")

def run_sliqsim(qasm_file):
    """Run SliQSim on the provided QASM file and return the statevector."""
    result = subprocess.run(
        [SLIQSIM_PATH, "--sim_qasm", qasm_file, "--type", "1"],
        capture_output=True,
        text=True
    )
    
    if result.returncode != 0:
        print(f"Error running SliQSim: {result.stderr}")
        return None
    
    try:
        # Find the JSON part in the output
        output = result.stdout
        json_start = output.find("{")
        json_end = output.rfind("}") + 1
        json_str = output[json_start:json_end]
        
        # Pre-process the output to make it valid JSON
        # Convert complex numbers like 0.707107+0.707107i to strings
        import re
        complex_pattern = r'(\d+\.\d+)([+-]\d+\.\d+)i'
        json_str = re.sub(complex_pattern, r'"\1\2i"', json_str)
        
        data = json.loads(json_str)
        vector = data["statevector"]
        
        # Convert to complex numbers
        complex_vector = []
        for elem in vector:
            if isinstance(elem, str) and "i" in elem:
                # Parse complex number from string
                if "+" in elem:
                    parts = elem.split("+")
                    real_part = float(parts[0].strip('"'))
                    imag_part = float(parts[1].replace("i", "").strip('"'))
                elif "-" in elem[1:]:  # Check if minus sign is not the first character
                    first_minus = elem.find("-", 1)
                    real_part = float(elem[:first_minus].strip('"'))
                    imag_part = float(elem[first_minus:].replace("i", "").strip('"'))
                else:
                    real_part = 0.0
                    imag_part = float(elem.replace("i", "").strip('"'))
                complex_vector.append(complex(real_part, imag_part))
            else:
                # Handle real numbers
                if isinstance(elem, str):
                    elem = float(elem.strip('"'))
                complex_vector.append(complex(elem, 0))
        return complex_vector
    except Exception as e:
        print(f"Error parsing output: {e}")
        print(f"Output was: {result.stdout}")
        return None

def expected_cp_statevector(basis_state, num_qubits, control, target, angle):
    """Generate expected statevector after CP gate application."""
    vector = np.zeros(2**num_qubits, dtype=complex)
    
    state_idx = int(basis_state[::-1], 2)
    vector[state_idx] = 1.0
    
    # Check if both control and target are 1
    if basis_state[control] == '1' and basis_state[target] == '1':
        # Apply phase
        phase = cmath.exp(1j * float(angle))
        vector[state_idx] = phase
    
    return vector

def expected_maj_statevector(basis_state, num_qubits, c1, c2, c3, target):
    """Generate expected statevector after MAJ gate application."""
    vector = np.zeros(2**num_qubits, dtype=complex)
    
    # Count 1s in control qubits
    control_sum = int(basis_state[c1]) + int(basis_state[c2]) + int(basis_state[c3])
    
    # Create a new basis state - in little-endian (q[0] first)
    new_state = list(basis_state)
    
    # Apply majority rule: flip target if majority (≥2) of controls are 1
    if control_sum >= 2:
        new_state[target] = '1' if basis_state[target] == '0' else '0'
    
    # Convert new state to integer index (after converting back to big-endian)
    new_state_idx = int(''.join(new_state)[::-1], 2)
    vector[new_state_idx] = 1.0
    
    return vector

def test_cp_gate():
    """Test the controlled-phase gate on all basis states."""
    print("Testing Controlled-Phase Gate...")
    num_qubits = 2
    control = 0
    target = 1
    angle = np.pi/4
    
    ensure_temp_dir()
    
    # Test all basis states
    for state_idx in range(2**num_qubits):
        basis_state = basis_state_to_binary(state_idx, num_qubits)
        filename = f"{TEMP_DIR}/cp_test_{basis_state}.qasm"
        
        # Print the basis state in both formats for clarity
        big_endian = basis_state[::-1]  # For display in |...⟩ notation
        print(f"  Testing basis state |{big_endian}⟩ (q[0]={basis_state[0]}, q[1]={basis_state[1]})")
        
        # Create test file
        create_test_qasm(
            filename, 
            basis_state, 
            num_qubits, 
            "cp", 
            {"control": control, "target": target, "angle": "pi/4"}
        )
        
        # Run simulator
        result = run_sliqsim(filename)
        
        if result is None:
            print(f"    Result: FAILED - Could not run simulation")
            continue
            
        # Generate expected result
        expected = expected_cp_statevector(basis_state, num_qubits, control, target, angle)
        
        # Convert result to numpy array for comparison
        result_array = np.array(result)
        
        # Compare (allowing for small numerical differences)
        is_close = np.allclose(result_array, expected, atol=1e-6)
        
        if is_close:
            print(f"    Result: PASSED")
        else:
            print(f"    Result: FAILED")
            print(f"    Expected: {expected}")
            print(f"    Got:      {result_array}")

def test_maj_gate():
    """Test the MAJ-controlled-X gate on all basis states."""
    print("\nTesting MAJ-Controlled-X Gate...")
    num_qubits = 4
    c1, c2, c3, target = 0, 1, 2, 3
    
    ensure_temp_dir()
    
    # Test representative basis states
    for control_pattern in [(0,0,0), (0,0,1), (0,1,0), (0,1,1),
                           (1,0,0), (1,0,1), (1,1,0), (1,1,1)]:
        for target_bit in [0, 1]:
            # Create basis state with these control and target bits
            basis_state = list('0000')
            basis_state[c1] = str(control_pattern[0])
            basis_state[c2] = str(control_pattern[1])
            basis_state[c3] = str(control_pattern[2])
            basis_state[target] = str(target_bit)
            basis_state = ''.join(basis_state)
            
            big_endian = basis_state[::-1]  # For display in |...⟩ notation
            
            filename = f"{TEMP_DIR}/maj_test_{''.join(basis_state)}.qasm"
            
            print(f"  Testing |{big_endian}⟩: controls={control_pattern}, target={target_bit}")
            
            # Create test file
            create_test_qasm(
                filename, 
                basis_state, 
                num_qubits, 
                "maj", 
                {"c1": c1, "c2": c2, "c3": c3, "target": target}
            )
            
            # Run simulator
            result = run_sliqsim(filename)
            
            if result is None:
                print(f"    Result: FAILED - Could not run simulation")
                continue
                
            # Generate expected result
            expected = expected_maj_statevector(basis_state, num_qubits, c1, c2, c3, target)
            
            # Convert result to numpy array for comparison
            result_array = np.array(result, dtype=complex)
            
            # Compare (allowing for small numerical differences)
            is_close = np.allclose(result_array, expected, atol=1e-6)
            
            if is_close:
                # Determine expected target value after gate
                control_sum = sum(control_pattern)
                new_target = (target_bit ^ 1) if control_sum >= 2 else target_bit
                print(f"    Result: PASSED (target {target_bit}→{new_target})")
            else:
                print(f"    Result: FAILED")
                print(f"    Expected: {expected}")
                print(f"    Got:      {result_array}")

if __name__ == "__main__":
    print("Starting SliQSim Gate Verification...")
    test_cp_gate()
    test_maj_gate()
    print("\nVerification complete.")