/* 
The interval bounds of the elements of the state vector are obtained by projecting the state invariant ellipsoid onto the plane of interest.
The state bounds are the following:
|x1| <= 2.398;
|x2| <= 0.756;
|x3| <= 6.818;
|x4| <= 18.633;

The interval bounds of the elements of the output vector are also obtained by projecting the output invariant ellipsoid onto the plane of interest.
The output bounds are the following:
|y1| <= 109.857;
|y2| <= 163.121;

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
Namely, in this example, lambda_min(P) = 0.0029 and lambda_max(P) = 6.9913; hence, we choose the values 0.0025 and 7 to be the lower and upper bound of lamda_min(P) and lambda_max(P), respectively.
Hence, norm_x_max = 1/sqrt(0.0025) = 20.

Output vector:
The radius of the error ball associated with the output vector is: r = 2 * 0
The maximum and minimum eigenvalues of the matrix Q (Q is the matrix that defines the output invariant ellipsoid) are computed using MATLAB's eig function.
To stay on the safe side, we manually choose a lower bound to the minimum eigenvalue of Q and an upper bound to the maximum eigenvalue of Q.
Namely, in this example, lambda_min(Q) = 3.5898e-5 and lambda_max(Q) = 9.2422e-5; hence, we choose the values 3.5e-5 and 1e-4 to be the lower and upper bound of lamda_min(Q) and lambda_max(Q), respectively.
Hence, norm_y_max = 1/sqrt(3.5e-5) = 169.9036.

*/

typedef struct { double x1, x2, x3, x4; } state;
typedef struct { double y1, y2; } output;

//@ predicate stateinv(real x1, real x2, real x3, real x4, real lambda) = 0.3278 * x1 * x1 + 2 * -0.9846 * x1 * x2 + 2 * 0.1045 * x1 * x3 + 2 * -0.0011 * x1 * x4 + 6.7872 * x2 * x2 + 2 * -0.6206 * x2 * x3 + 2 * 0.0243 * x2 * x4 + 0.0794 * x3 * x3 + 2 * -0.0019 * x3 * x4 + 0.003 * x4 * x4 <= lambda;

//@ predicate outputinv(real y1, real y2, real lambda) = 8.828e-05 * y1 * y1 + 2 * 1.473e-05 * y1 * y2 + 4.004e-05 * y2 * y2 <= lambda;


/*@
requires \valid(x);
requires \separated(&(x->x1),&(x->x2),&(x->x3),&(x->x4));
assigns *x;

behavior zero_input_real_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1);

behavior polytope_input_real_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1);
	 
behavior zero_input_float_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1 - 2 * 4 * 0 * 7 * 20 - 4 * 0 * 4 * 0 * 7);
	 
behavior polytope_input_float_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, 1 - 2 * 4 * 0 * 7 * 20 - 4 * 0 * 4 * 0 * 7);

*/

void updateState(state *x, double d1, double d2) {
	 double pre_x1 = x->x1, pre_x2 = x->x2, pre_x3 = x->x3, pre_x4 = x->x4;

	 x->x1 = 1 * pre_x1 + 0 * pre_x2 + 0.01 * pre_x3 + 0 * pre_x4 + 0 * d1 + 0 * d2;
	 x->x2 = 0 * pre_x1 + 1 * pre_x2 + 0 * pre_x3 + 0.01 * pre_x4 + 0 * d1 + 0 * d2;
	 x->x3 = -0.1025 * pre_x1 + 0.6433 * pre_x2 + 0.8553 * pre_x3 + 0.1498 * pre_x4 + 0 * d1 + 0 * d2;
	 x->x4 = 0.6149 * pre_x1 + -9.8597 * pre_x2 + 0.8684 * pre_x3 + -0.099 * pre_x4 + 6 * d1 + 20 * d2;

}

/*@
requires \valid(x) && \valid(y);
requires \separated(&(x->x1),&(x->x2),&(x->x3),&(x->x4),&(y->y1),&(y->y2));
assigns *y;

behavior zero_input_real_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1);

behavior polytope_input_real_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1);
	 
behavior zero_input_float_model:
	 assumes d1 == 0 && d2 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1 - 2 * 2 * 0 * 1e-4 * 169.9036 - 2 * 0 * 2 * 0 * 1e-4);

behavior polytope_input_float_model:
	 assumes -0.3 <= d1 <= 0.3 && -0.0015 <= d2 <= 0.0015 && -0.3 <= d1+d2 <= 0.3;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), 1) ==> outputinv(y->y1, y->y2, 1 - 2 * 2 * 0 * 1e-4 * 169.9036 - 2 * 0 * 2 * 0 * 1e-4);

*/

void updateOutput(state *x, output *y, double d1, double d2) {
	 double pre_x1 = x->x1, pre_x2 = x->x2, pre_x3 = x->x3, pre_x4 = x->x4;
	 
	 y->y1 = -3 * pre_x1 + 3 * pre_x2 + 0 * pre_x3 + 0 * pre_x4 + 0 * d1 + 0 * d2;
	 y->y2 = 0 * pre_x1 + -30 * pre_x2 + 0 * pre_x3 + 0 * pre_x4 + 30 * d1 + 0 * d2;

 }
