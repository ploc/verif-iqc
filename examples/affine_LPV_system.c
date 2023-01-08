/* 
The interval bounds of the elements of the state vector are obtained by projecting the state invariant ellipsoid onto the plane of interest.
The state bounds are the following:
|x1| <= 2.7465;
|x2| <= 1.5403;
|x3| <= 14.1678;
|x4| <= 41.8491;

The interval bounds of the elements of the output vector are also obtained by projecting the output invariant ellipsoid onto the plane of interest.
The output bounds are the following:
|y1| <= 9.2913;
|y2| <= 67.4139;

The floating point errors of each element of the state and output vectors are computed using the tiny tool, and their values are the following:
State errors:
e1 =
e2 =
e3 =
e4 =

Output errors:
e1 =
e2 =

Float Model Analysis:

State vector:
The radius of the error ball associated with the state vector is: r = 4 * 0
The maximum and minimum eigenvalues of the matrix P (P is the matrix that defines the state invariant ellipsoid) are computed using MATLAB's eig function.
MATLAB's algorithms for computing the eigenvalues of a positive definite matrix are generally accurate.
Nevertheless, to stay on the safe side, we manually choose a lower bound to the minimum eigenvalue of P and an upper bound to the maximum eigenvalue of P.
Namely, in this example, lambda_min(P) = 0.0006 and lambda_max(P) = 2.3098; hence, we choose the values 0.0004 and 2.32 to be the lower and upper bound of lamda_min(P) and lambda_max(P), respectively.
Hence, norm_x_max = 1/sqrt(0.0004) = 50.

Output vector:
The radius of the error ball associated with the output vector is: r = 2 * 0
The maximum and minimum eigenvalues of the matrix Q (Q is the matrix that defines the output invariant ellipsoid) are computed using MATLAB's eig function.
To stay on the safe side, we manually choose a lower bound to the minimum eigenvalue of Q and an upper bound to the maximum eigenvalue of Q.
Namely, in this example, lambda_min(Q) = 0.0002 and lambda_max(Q) = 0.0117; hence, we choose the values 0.0001 and 0.013 to be the lower and upper bound of lamda_min(Q) and lambda_max(Q), respectively.
Hence, norm_y_max = 1/sqrt(0.0001) = 100.

*/

typedef struct { double x1, x2, x3, x4; } state;
typedef struct { double y1, y2; } output;

//@ predicate stateinv(real x1, real x2, real x3, real x4, real lambda) = 0.34884 * x1 * x1 + 2 * -0.65947 * x1 * x2 + 2 * 0.057429 * x1 * x3 + 2 * -6e-06 * x1 * x4 + 2.0724 * x2 * x2 + 2 * -0.16937 * x2 * x3 + 2 * 0.004972 * x2 * x4 + 0.018915 * x3 * x3 + 2 * -0.000334 * x3 * x4 + 0.000601 * x4 * x4 <= lambda;

//@ predicate outputinv(real y1, real y2, real lambda) = 0.011655 * y1 * y1 + 2 * 0.0001259 * y1 * y2 + 0.0002214 * y2 * y2 <= lambda;

/*@
requires \valid(x);
requires \separated(&(x->x1),&(x->x2),&(x->x3),&(x->x4));
requires -1 <= delta1 <= 1 && -1 <= delta2 <= 1;
assigns *x;

behavior zero_input_real_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1);

behavior polytope_input_real_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1);
	 
behavior zero_input_float_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1 - 2 * 4 * 0 * 2.32 * 50 - 4 * 0 * 4 * 0 * 2.32);
	 
behavior polytope_input_float_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1 - 2 * 4 * 0 * 2.32 * 50 - 4 * 0 * 4 * 0 * 2.32);
*/

void updateState(state *x, double delta1, double delta2, double d1, double d2) {
	 double pre_x1 = x->x1, pre_x2 = x->x2, pre_x3 = x->x3, pre_x4 = x->x4;

	 x->x1 = 1 * pre_x1 + 0 * pre_x2 + 0.01 * pre_x3 + 0 * pre_x4 + 0 * d1 + 0 * d2;
 	 x->x2 = 0 * pre_x1 + 1 * pre_x2 + 0 * pre_x3 + 0.01 * pre_x4 + 0 * d1 + 0 * d2;
 	 x->x3 = -0.0973 * pre_x1 + delta1 * -0.02 * pre_x1 + 0.4823 * pre_x2 + delta1 * 0.02 * pre_x2 + 0.8648 * pre_x3 + 0.1473 * pre_x4 + 0 * d1 + 0 * d2;
 	 x->x4 = 0.5837 * pre_x1 + delta1 * 0.12 * pre_x1 + -8.8940 * pre_x2 + delta1 * -0.12 * pre_x2 + delta2 * -1.2 * pre_x2 + 0.8113 *pre_x3 + -0.0837 * pre_x4 + 6 * d1 + delta2 * 1.2 * d1 + 20 * d2;

}

/*@
requires \valid(x) && \valid(y);
requires \separated(&(x->x1),&(x->x2),&(x->x3),&(x->x4),&(y->y1),&(y->y2));
requires -1 <= delta1 <= 1 && -1 <= delta2 <= 1;
assigns *y;

behavior zero_input_real_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1);

behavior polytope_input_real_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1);
	 
behavior zero_input_float_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1 - 2 * 2 * 0 * 0.013 * 100 - 2 * 0 * 2 * 0 * 0.013);

behavior polytope_input_float_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1 - 2 * 2 * 0 * 0.013 * 100 - 2 * 0 * 2 * 0 * 0.013);
*/

void updateOutput(state *x, output *y, double delta1, double delta2, double d1, double d2) {
	 double pre_x1 = x->x1, pre_x2 = x->x2, pre_x3 = x->x3, pre_x4 = x->x4;

	 y->y1 = -3 * pre_x1 + delta1 * -0.6 * pre_x1 + 3 * pre_x2 + delta1 * 0.6 * pre_x2 + 0 * pre_x3 + 0 * pre_x4 + 0 * d1 + 0 * d2;
 	 y->y2 = 0 * pre_x1 + -30 * pre_x2 + delta2 * -6 * pre_x2 + 0 * pre_x3 + 0 * pre_x4 + 30 * d1 + delta2 * 6 * d1 + 0 * d2;

 }
