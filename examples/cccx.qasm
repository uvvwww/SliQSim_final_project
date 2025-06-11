OPENQASM 2.0;
include "qelib1.inc";

qreg q[4];
creg c[4];
x q[0];
x q[1];
x q[2];
x q[3];

h q[3];
cu1(pi/2) q[2], q[3];
ccx q[0], q[1], q[2];
cu1(-pi/2) q[2], q[3];
ccx q[0], q[1], q[2];
cu1(pi/4) q[1], q[3];
cx q[0], q[1];
cu1(-pi/4) q[1], q[3];
cx q[0], q[1];
cu1(pi/4) q[0], q[3];
h q[3];