OPENQASM 2.0;
include "qelib1.inc";

qreg q[2];
creg c[2];

h q[1];
x q[0];
cp(pi/4) q[0], q[1];
h q[1];