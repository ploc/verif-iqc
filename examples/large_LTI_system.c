/* 
The interval bounds of the elements of the state vector are obtained by projecting the state invariant ellipsoid onto the plane of interest.
The state bounds are the following:
|x1| <= 10.4331;
|x2| <= 9.3613;
|x3| <= 10.2649;
|x4| <= 4.8187;
|x5| <= 8.5475;
|x6| <= 4.1197;
|x7| <= 17.5804;
|x8| <= 5.4132;
|x9| <= 4.7693;
|x10| <= 2.5524;
|x11| <= 3.2844;
|x12| <= 3.7161;
|x13| <= 6.1067;
|x14| <= 1.8785;
|x15| <= 1.5947;
|x16| <= 9.2954;

The interval bounds of the elements of the output vector are also obtained by projecting the output invariant ellipsoid onto the plane of interest.
The output bounds are the following:
|y1| <= 9.0637;
|y2| <= 14.8132;
|y3| <= 24.7371;
|y4| <= 1.6384;

The floating point errors of each element of the state and output vectors are computed using the tiny tool, and their values are the following:
State errors:
x10:1.411699E-13
x11:1.414911E-13
x12:1.374805E-13
x13:1.404930E-13
x14:1.331288E-13
x15:1.367513E-13
x16:1.408495E-13
x1:1.587635E-13
x2:1.660575E-13
x3:1.603789E-13
x4:1.414581E-13
x5:1.680394E-13
x6:1.471209E-13
x7:1.752915E-13
x8:1.513350E-13
x9:1.529184E-13

Output errors:
y1:1.722271E-13
y2:2.375678E-13
y3:2.402908E-13
y4:1.329628E-13

Float Model Analysis:

State vector:
The radius of the error ball associated with the state vector is: r = 16 * 1.752915e-13
The maximum and minimum eigenvalues of the matrix P (P is the matrix that defines the state invariant ellipsoid) are computed using MATLAB's eig function.
MATLAB's algorithms for computing the eigenvalues of a positive definite matrix are generally accurate.
Nevertheless, to stay on the safe side, we manually choose a lower bound to the minimum eigenvalue of P and an upper bound to the maximum eigenvalue of P.
Namely, in this example, lambda_min(P) = 0.0031 and lambda_max(P) = 8.5188; hence, we choose the values 0.003 and 8.55 to be the lower and upper bound of lamda_min(P) and lambda_max(P), respectively.
Hence, norm_x_max = 1/sqrt(0.003) = 18.2574.

Output vector:
The radius of the error ball associated with the output vector is: r = 4 * 2.402908E-13
The maximum and minimum eigenvalues of the matrix Q (Q is the matrix that defines the output invariant ellipsoid) are computed using MATLAB's eig function.
To stay on the safe side, we manually choose a lower bound to the minimum eigenvalue of Q and an upper bound to the maximum eigenvalue of Q.
Namely, in this example, lambda_min(Q) = 0.0015 and lambda_max(Q) = 0.3750; hence, we choose the values 0.001 and 0.38 to be the lower and upper bound of lamda_min(Q) and lambda_max(Q), respectively.
Hence, norm_y_max = 1/sqrt(0.001) = 31.6228.

*/

typedef struct { double x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16; } state;
typedef struct { double y1, y2, y3, y4; } output;

//@ predicate stateinv(real x1, real x2, real x3, real x4, real x5, real x6, real x7, real x8, real x9, real x10, real x11, real x12, real x13, real x14, real x15, real x16, real lambda) = 0.01274 * x1 * x1 + 2 * 0.00159 * x1 * x2 + 2 * -0.00684 * x1 * x3 + 2 * -0.00017 * x1 * x4 + 2 * -0.0005 * x1 * x5 + 2 * 0.00017 * x1 * x6 + 2 * 0.00053 * x1 * x7 + 2 * -0.00233 * x1 * x8 + 2 * 0.00063 * x1 * x9 + 2 * 0.00017 * x1 * x10 + 2 * 0.0013 * x1 * x11 + 2 * 0.00071 * x1 * x12 + 2 * 0.00018 * x1 * x13 + 2 * 0.00302 * x1 * x14 + 2 * 0.01688 * x1 * x15 + 2 * -0.00126 * x1 * x16 + 0.01506 * x2 * x2 + 2 * -0.00045 * x2 * x3 + 2 * 0.00107 * x2 * x4 + 2 * -0.00853 * x2 * x5 + 2 * 7e-05 * x2 * x6 + 2 * 0.00152 * x2 * x7 + 2 * -0.00141 * x2 * x8 + 2 * 0.0024 * x2 * x9 + 2 * -0.0001 * x2 * x10 + 2 * 0.0056 * x2 * x11 + 2 * 0.00125 * x2 * x12 + 2 * -0.00019 * x2 * x13 + 2 * 0.00189 * x2 * x14 + 2 * 0.02127 * x2 * x15 + 2 * -0.00105 * x2 * x16 + 0.01517 * x3 * x3 + 2 * -0.00189 * x3 * x4 + 2 * 0.00042 * x3 * x5 + 2 * -0.00015 * x3 * x6 + 2 * -0.0008 * x3 * x7 + 2 * 0.01078 * x3 * x8 + 2 * 0.00462 * x3 * x9 + 2 * -0.00136 * x3 * x10 + 2 * -0.00078 * x3 * x11 + 2 * -0.00069 * x3 * x12 + 2 * -0.00064 * x3 * x13 + 2 * -0.00499 * x3 * x14 + 2 * -0.01975 * x3 * x15 + 2 * 0.00203 * x3 * x16 + 0.04526 * x4 * x4 + 2 * 0.00256 * x4 * x5 + 2 * 0.00565 * x4 * x6 + 2 * -0.00047 * x4 * x7 + 2 * 0.00124 * x4 * x8 + 2 * 0.00055 * x4 * x9 + 2 * -0.00765 * x4 * x10 + 2 * 0.00044 * x4 * x11 + 2 * 0.00049 * x4 * x12 + 2 * -0.00377 * x4 * x13 + 2 * -0.01805 * x4 * x14 + 2 * 0.00037 * x4 * x15 + 2 * 0.00424 * x4 * x16 + 0.02394 * x5 * x5 + 2 * -0.00434 * x5 * x6 + 2 * -0.00486 * x5 * x7 + 2 * 0.00779 * x5 * x8 + 2 * 0.00428 * x5 * x9 + 2 * -0.00263 * x5 * x10 + 2 * -0.01147 * x5 * x11 + 2 * -0.00229 * x5 * x12 + 2 * -0.0004 * x5 * x13 + 2 * -0.01029 * x5 * x14 + 2 * -0.05332 * x5 * x15 + 2 * 0.00383 * x5 * x16 + 0.06204 * x6 * x6 + 2 * -0.00049 * x6 * x7 + 2 * 9e-05 * x6 * x8 + 2 * 0.00104 * x6 * x9 + 2 * -0.00664 * x6 * x10 + 2 * -0.00303 * x6 * x11 + 2 * 2e-05 * x6 * x12 + 2 * -0.0021 * x6 * x13 + 2 * -0.02877 * x6 * x14 + 2 * 0.00872 * x6 * x15 + 2 * 0.0073 * x6 * x16 + 0.00483 * x7 * x7 + 2 * -0.00425 * x7 * x8 + 2 * -0.00322 * x7 * x9 + 2 * -0.00027 * x7 * x10 + 2 * 0.00447 * x7 * x11 + 2 * 0.00262 * x7 * x12 + 2 * 0.0049 * x7 * x13 + 2 * 0.01725 * x7 * x14 + 2 * 0.02201 * x7 * x15 + 2 * -0.00681 * x7 * x16 + 0.06032 * x8 * x8 + 2 * 0.03424 * x8 * x9 + 2 * 0.00164 * x8 * x10 + 2 * -0.0229 * x8 * x11 + 2 * -0.00219 * x8 * x12 + 2 * 0.00151 * x8 * x13 + 2 * -0.0039 * x8 * x14 + 2 * -0.0416 * x8 * x15 + 2 * 0.00211 * x8 * x16 + 0.06682 * x9 * x9 + 2 * 0.00299 * x9 * x10 + 2 * -0.01782 * x9 * x11 + 2 * -0.00467 * x9 * x12 + 2 * -0.0004 * x9 * x13 + 2 * -0.01381 * x9 * x14 + 2 * -0.05155 * x9 * x15 + 2 * 0.00514 * x9 * x16 + 0.17462 * x10 * x10 + 2 * 0.00546 * x10 * x11 + 2 * -0.00381 * x10 * x12 + 2 * 0.00595 * x10 * x13 + 2 * 0.06247 * x10 * x14 + 2 * -0.01668 * x10 * x15 + 2 * -0.00051 * x10 * x16 + 0.11464 * x11 * x11 + 2 * -0.00107 * x11 * x12 + 2 * 0.00579 * x11 * x13 + 2 * 0.04811 * x11 * x14 + 2 * 0.08384 * x11 * x15 + 2 * -0.01848 * x11 * x16 + 0.08902 * x12 * x12 + 2 * -0.04115 * x12 * x13 + 2 * -0.16745 * x12 * x14 + 2 * 0.06251 * x12 * x15 + 2 * 0.0664 * x12 * x16 + 0.37106 * x13 * x13 + 2 * 1.1238 * x13 * x14 + 2 * -0.24536 * x13 * x15 + 2 * -0.43802 * x13 * x16 + 7.4259 * x14 * x14 + 2 * -1.4728 * x14 * x15 + 2 * -2.0756 * x14 * x16 + 0.96509 * x15 * x15 + 2 * 0.4021 * x15 * x16 + 0.67176 * x16 * x16 <= lambda;

//@ predicate outputinv(real y1, real y2, real y3, real y4, real lambda) = 0.01221 * y1 * y1 + 2 * 0.00014 * y1 * y2 + 2 * -0.0002 * y1 * y3 + 2 * -0.00037 * y1 * y4 + 0.00551 * y2 * y2 + 2 * 0.00137 * y2 * y3 + 2 * 0.00034 * y2 * y4 + 0.00199 * y3 * y3 + 2 * 0.00209 * y3 * y4 + 0.37503 * y4 * y4 <= lambda;

/*@
requires \valid(x);
requires \separated(&(x->x1),&(x->x2),&(x->x3),&(x->x4),&(x->x5),&(x->x6),&(x->x7),&(x->x8),&(x->x9),&(x->x10),&(x->x11),&(x->x12),&(x->x13),&(x->x14),&(x->x15),&(x->x16));
assigns *x;

behavior zero_input_real_model:
	 assumes d1 == 0 && d2 == 0 && d3 == 0 && d4 == 0 && d5 == 0 && d6 == 0 && d7 == 0 && d8 == 0 && d9 == 0 && d10 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, x->x5, x->x6, x->x7, x->x8, x->x9, x->x10, x->x11, x->x12, x->x13, x->x14, x->x15, x->x16, 1);

behavior polytope_input_real_model:
	 assumes -0.17786 <= d1 <= 0.17786 && -0.24119 <= d2 <= 0.24119 && -0.41152 <= d3 <= 0.41152 && -8.5914 <= d4 <= 8.5914 && -0.13755 <= d5 <= 0.13755 && -0.14191 <= d6 <= 0.14191 && -0.3605 <= d7 <= 0.3605 && -5.2603 <= d8 <= 5.2603 && -8.8649 <= d9 <= 8.8649 && -6.3586 <= d10 <= 6.3586;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, x->x5, x->x6, x->x7, x->x8, x->x9, x->x10, x->x11, x->x12, x->x13, x->x14, x->x15, x->x16, 1);
	 
	 behavior zero_input_float_model:
	 assumes d1 == 0 && d2 == 0 && d3 == 0 && d4 == 0 && d5 == 0 && d6 == 0 && d7 == 0 && d8 == 0 && d9 == 0 && d10 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, x->x5, x->x6, x->x7, x->x8, x->x9, x->x10, x->x11, x->x12, x->x13, x->x14, x->x15, x->x16, 1 - 2 * 16 * 1.752915e-13 * 8.55 * 18.2574 - 16 * 1.752915e-13 * 16 * 1.752915e-13 * 8.55);

behavior polytope_input_float_model:
	 assumes -0.17786 <= d1 <= 0.17786 && -0.24119 <= d2 <= 0.24119 && -0.41152 <= d3 <= 0.41152 && -8.5914 <= d4 <= 8.5914 && -0.13755 <= d5 <= 0.13755 && -0.14191 <= d6 <= 0.14191 && -0.3605 <= d7 <= 0.3605 && -5.2603 <= d8 <= 5.2603 && -8.8649 <= d9 <= 8.8649 && -6.3586 <= d10 <= 6.3586;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> stateinv(x->x1, x->x2, x->x3, x->x4, x->x5, x->x6, x->x7, x->x8, x->x9, x->x10, x->x11, x->x12, x->x13, x->x14, x->x15, x->x16, 1 - 2 * 16 * 1.752915e-13 * 8.55 * 18.2574 - 16 * 1.752915e-13 * 16 * 1.752915e-13 * 8.55);

*/

void updateState(state *x, double d1, double d2, double d3, double d4, double d5, double d6, double d7, double d8, double d9, double d10) {
	 double pre_x1 = x->x1, pre_x2 = x->x2, pre_x3 = x->x3, pre_x4 = x->x4, pre_x5 = x->x5, pre_x6 = x->x6, pre_x7 = x->x7, pre_x8 = x->x8, pre_x9 = x->x9, pre_x10 = x->x10, pre_x11 = x->x11, pre_x12 = x->x12, pre_x13 = x->x13, pre_x14 = x->x14, pre_x15 = x->x15, pre_x16 = x->x16;

	 x->x1 = 0.0191 * pre_x1 + -0.8282 * pre_x2 + -0.0939 * pre_x3 + 0.0204 * pre_x4 + 0.0025 * pre_x5 + -0.0132 * pre_x6 + 0.0118 * pre_x7 + 0.1485 * pre_x8 + 0.0268 * pre_x9 + -0.0002 * pre_x10 + -0.0049 * pre_x11 + 0.0002 * pre_x12 + 0.0004 * pre_x13 + 0.0002 * pre_x14 + 0.0003 * pre_x15 + 0.0005 * pre_x16 + -0.2705 * d1 + -0.0021 * d2 + 0.2905 * d3 + -0.0001 * d4 + -1.6135 * d5 + -0.0033 * d6 + 1.2417 * d7 + 0 * d8 + -0.0005 * d9 + 0 * d10;
	 x->x2 = 0.8408 * pre_x1 + 0.1735 * pre_x2 + -0.0212 * pre_x3 + -0.0406 * pre_x4 + 0.0993 * pre_x5 + -0.0098 * pre_x6 + 0.0102 * pre_x7 + 0.1881 * pre_x8 + 0.0497 * pre_x9 + 0.0063 * pre_x10 + -0.0271 * pre_x11 + -0.0021 * pre_x12 + 0.0009 * pre_x13 + -0.001 * pre_x14 + -0.0057 * pre_x15 + 0.0009 * pre_x16 + -0.4045 * d1 + 0.0044 * d2 + 0.1619 * d3 + 0.0002 * d4 + -0.8561 * d5 + 0.0583 * d6 + -0.3968 * d7 + 0 * d8 + 0.0002 * d9 + -0.0003 * d10;
	 x->x3 = 0.1682 * pre_x1 + 0.0462 * pre_x2 + -0.1397 * pre_x3 + 0.023 * pre_x4 + -0.6037 * pre_x5 + 0.0194 * pre_x6 + 0.0689 * pre_x7 + 0.0972 * pre_x8 + -0.2081 * pre_x9 + -0.0133 * pre_x10 + 0.0299 * pre_x11 + 0.0019 * pre_x12 + -0.0018 * pre_x13 + -0.0068 * pre_x14 + -0.0348 * pre_x15 + 0.0018 * pre_x16 + 0.0321 * d1 + -0.0087 * d2 + 0.9258 * d3 + -0.0002 * d4 + 1.1103 * d5 + -0.0958 * d6 + 1.41 * d7 + 0.0001 * d8 + -0.0002 * d9 + 0.0005 * d10;
	 x->x4 = -0.0189 * pre_x1 + 0.0287 * pre_x2 + -0.0652 * pre_x3 + -0.0217 * pre_x4 + -0.0399 * pre_x5 + -0.5493 * pre_x6 + 0.0094 * pre_x7 + -0.0131 * pre_x8 + -0.0068 * pre_x9 + 0.2481 * pre_x10 + 0.0088 * pre_x11 + -0.0032 * pre_x12 + 0.0103 * pre_x13 + -0.0001 * pre_x14 + 0.0085 * pre_x15 + 0.0143 * pre_x16 + 0.0087 * d1 + 0.1856 * d2 + 0.0284 * d3 + 0.0017 * d4 + -0.0371 * d5 + 1.8827 * d6 + 0.0925 * d7 + -0.0003 * d8 + 0 * d9 + -0.0043 * d10;
	 x->x5 = 0.0371 * pre_x1 + -0.1 * pre_x2 + 0.5701 * pre_x3 + -0.0411 * pre_x4 + 0.3847 * pre_x5 + -0.0429 * pre_x6 + 0.1007 * pre_x7 + 0.1021 * pre_x8 + -0.3973 * pre_x9 + -0.0025 * pre_x10 + 0.0197 * pre_x11 + -0.0017 * pre_x12 + -0.0008 * pre_x13 + -0.0012 * pre_x14 + -0.0056 * pre_x15 + 0.0017 * pre_x16 + 0.0232 * d1 + 0.0102 * d2 + 0.6745 * d3 + -0.0001 * d4 + 0.4131 * d5 + 0.1148 * d6 + 0.0219 * d7 + -0.0001 * d8 + 0 * d9 + -0.0007 * d10;
	 x->x6 = -0.0027 * pre_x1 + 0.0289 * pre_x2 + 0.0407 * pre_x3 + 0.5489 * pre_x4 + 0.0136 * pre_x5 + 0.5947 * pre_x6 + 0.0073 * pre_x7 + 0.0391 * pre_x8 + -0.0099 * pre_x9 + 0.3524 * pre_x10 + 0.0027 * pre_x11 + -0.0037 * pre_x12 + 0.0154 * pre_x13 + 0.0002 * pre_x14 + 0.0111 * pre_x15 + 0.0067 * pre_x16 + -0.0101 * d1 + 0.0853 * d2 + 0.0263 * d3 + -0.0012 * d4 + -0.0789 * d5 + 0.4681 * d6 + 0.045 * d7 + 0.0004 * d8 + 0 * d9 + 0.006 * d10;
	 x->x7 = -0.0185 * pre_x1 + 0.0252 * pre_x2 + -0.0707 * pre_x3 + -0.0107 * pre_x4 + 0.0496 * pre_x5 + 0.0142 * pre_x6 + 0.9758 * pre_x7 + -0.063 * pre_x8 + 0.0939 * pre_x9 + -0.0043 * pre_x10 + 0.0249 * pre_x11 + 0.0032 * pre_x12 + -0.001 * pre_x13 + 0.001 * pre_x14 + 0.006 * pre_x15 + -0.0011 * pre_x16 + 0.012 * d1 + -0.0032 * d2 + 0.0946 * d3 + 0 * d4 + -0.0971 * d5 + -0.0182 * d6 + -0.0278 * d7 + 0 * d8 + 0 * d9 + -0.0001 * d10;
	 x->x8 = 0.129 * pre_x1 + -0.1839 * pre_x2 + -0.0384 * pre_x3 + 0.0462 * pre_x4 + 0.0814 * pre_x5 + -0.0019 * pre_x6 + 0.0497 * pre_x7 + -0.3332 * pre_x8 + -0.06 * pre_x9 + 0.0275 * pre_x10 + -0.3495 * pre_x11 + -0.0247 * pre_x12 + 0.0005 * pre_x13 + -0.035 * pre_x14 + -0.1778 * pre_x15 + 0.0112 * pre_x16 + 0.4659 * d1 + 0.0053 * d2 + -0.6207 * d3 + 0.0002 * d4 + 0.5881 * d5 + 0.0501 * d6 + -0.0537 * d7 + -0.0001 * d8 + 0.0004 * d9 + -0.0003 * d10;
	 x->x9 = 0.0005 * pre_x1 + -0.0306 * pre_x2 + -0.2398 * pre_x3 + -0.0129 * pre_x4 + 0.3432 * pre_x5 + 0.0473 * pre_x6 + -0.0798 * pre_x7 + 0.0207 * pre_x8 + 0.1303 * pre_x9 + 0.0171 * pre_x10 + 0.3274 * pre_x11 + 0.0272 * pre_x12 + -0.0097 * pre_x13 + -0.0507 * pre_x14 + -0.2532 * pre_x15 + 0.0209 * pre_x16 + 0.0554 * d1 + 0.0059 * d2 + 0.4495 * d3 + 0 * d4 + 0.2293 * d5 + 0.0174 * d6 + -0.0878 * d7 + 0 * d8 + 0 * d9 + 0.0003 * d10;
	 x->x10 = 0.0005 * pre_x1 + 0.0115 * pre_x2 + -0.007 * pre_x3 + 0.2624 * pre_x4 + 0.0382 * pre_x5 + -0.3765 * pre_x6 + 0.0042 * pre_x7 + 0.0216 * pre_x8 + -0.0112 * pre_x9 + 0.3357 * pre_x10 + 0.0217 * pre_x11 + 0.0091 * pre_x12 + 0.0301 * pre_x13 + -0.0105 * pre_x14 + -0.0337 * pre_x15 + -0.0867 * pre_x16 + -0.002 * d1 + -0.0329 * d2 + 0.0338 * d3 + -0.0012 * d4 + -0.0124 * d5 + -0.3293 * d6 + 0.0035 * d7 + 0.0001 * d8 + 0 * d9 + 0.0017 * d10;
	 x->x11 = 0.0059 * pre_x1 + 0.0711 * pre_x2 + 0.0393 * pre_x3 + -0.012 * pre_x4 + 0.1127 * pre_x5 + 0.0001 * pre_x6 + -0.0099 * pre_x7 + -0.1737 * pre_x8 + 0.0285 * pre_x9 + -0.0153 * pre_x10 + 0.5277 * pre_x11 + 0.0387 * pre_x12 + 0.0161 * pre_x13 + -0.0112 * pre_x14 + -0.0626 * pre_x15 + 0.0068 * pre_x16 + 0.093 * d1 + -0.0047 * d2 + -0.2128 * d3 + 0.0006 * d4 + -0.1102 * d5 + -0.0119 * d6 + 0.4025 * d7 + 0 * d8 + 0.0001 * d9 + -0.0003 * d10;
	 x->x12 = -0.0017 * pre_x1 + 0.0072 * pre_x2 + -0.0045 * pre_x3 + -0.0061 * pre_x4 + 0.013 * pre_x5 + 0.0036 * pre_x6 + -0.002 * pre_x7 + -0.0044 * pre_x8 + -0.0288 * pre_x9 + 0.0184 * pre_x10 + -0.1201 * pre_x11 + 0.9811 * pre_x12 + 0.0066 * pre_x13 + 0.0054 * pre_x14 + 0.0096 * pre_x15 + 0.012 * pre_x16 + 0.0085 * d1 + 0.0033 * d2 + 0.0016 * d3 + -0.0036 * d4 + -0.0153 * d5 + -0.0016 * d6 + 0.0243 * d7 + 0 * d8 + 0 * d9 + 0 * d10;
	 x->x13 = 0 * pre_x1 + -0.001 * pre_x2 + -0.0023 * pre_x3 + 0.0226 * pre_x4 + -0.0011 * pre_x5 + -0.0088 * pre_x6 + 0 * pre_x7 + -0.004 * pre_x8 + -0.0084 * pre_x9 + -0.134 * pre_x10 + 0.0043 * pre_x11 + 0.0072 * pre_x12 + 0.9577 * pre_x13 + -0.0156 * pre_x14 + -0.0099 * pre_x15 + -0.0404 * pre_x16 + 0.0008 * d1 + -0.0173 * d2 + 0.0108 * d3 + 0.0147 * d4 + -0.001 * d5 + 0.0123 * d6 + -0.0115 * d7 + 0 * d8 + 0 * d9 + -0.0003 * d10;
	 x->x14 = -0.0007 * pre_x1 + 0.0022 * pre_x2 + -0.0034 * pre_x3 + -0.002 * pre_x4 + -0.0047 * pre_x5 + 0.003 * pre_x6 + -0.0028 * pre_x7 + -0.0333 * pre_x8 + -0.0361 * pre_x9 + 0.019 * pre_x10 + -0.0092 * pre_x11 + -0.0066 * pre_x12 + -0.0066 * pre_x13 + 0.8915 * pre_x14 + -0.1308 * pre_x15 + 0.0011 * pre_x16 + 0.0307 * d1 + 0.0094 * d2 + 0.0289 * d3 + 0.006 * d4 + -0.0232 * d5 + -0.0061 * d6 + -0.0103 * d7 + 0 * d8 + 0 * d9 + -0.0001 * d10;
	 x->x15 = -0.0038 * pre_x1 + 0.0136 * pre_x2 + -0.0173 * pre_x3 + 0 * pre_x4 + -0.0162 * pre_x5 + 0.0027 * pre_x6 + -0.0143 * pre_x7 + -0.1538 * pre_x8 + -0.1769 * pre_x9 + 0.0004 * pre_x10 + -0.0686 * pre_x11 + -0.0432 * pre_x12 + -0.013 * pre_x13 + -0.1345 * pre_x14 + 0.2439 * pre_x15 + 0.0531 * pre_x16 + 0.1631 * d1 + -0.008 * d2 + 0.139 * d3 + 0.0009 * d4 + -0.1188 * d5 + -0.0088 * d6 + -0.0414 * d7 + 0 * d8 + 0.0001 * d9 + -0.0003 * d10;
	 x->x16 = 0.0003 * pre_x1 + -0.0025 * pre_x2 + 0.0016 * pre_x3 + -0.0061 * pre_x4 + -0.0035 * pre_x5 + 0.0034 * pre_x6 + 0.0009 * pre_x7 + 0.0022 * pre_x8 + 0.0119 * pre_x9 + 0.0591 * pre_x10 + 0.019 * pre_x11 + 0.0059 * pre_x12 + 0.0096 * pre_x13 + -0.0014 * pre_x14 + 0.0458 * pre_x15 + 0.873 * pre_x16 + -0.0114 * d1 + -0.0288 * d2 + -0.0044 * d3 + 0.0277 * d4 + 0.0082 * d5 + -0.001 * d6 + -0.0052 * d7 + 0 * d8 + 0 * d9 + -0.0003 * d10;

}
/*@
requires \valid(x) && \valid(y);
requires \separated(&(x->x1),&(x->x2),&(x->x3),&(x->x4),&(x->x5),&(x->x6),&(x->x7),&(x->x8),&(x->x9),&(x->x10),&(x->x11),&(x->x12),&(x->x13),&(x->x14),&(x->x15),&(x->x16),&(y->y1),&(y->y2),&(y->y3),&(y->y4));
assigns *y;

behavior zero_input_real_model:
	 assumes d1 == 0 && d2 == 0 && d3 == 0 && d4 == 0 && d5 == 0 && d6 == 0 && d7 == 0 && d8 == 0 && d9 == 0 && d10 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> outputinv(y->y1, y->y2, y->y3, y->y4, 1);

behavior polytope_input_real_model:
	 assumes -0.17786 <= d1 <= 0.17786 && -0.24119 <= d2 <= 0.24119 && -0.41152 <= d3 <= 0.41152 && -8.5914 <= d4 <= 8.5914 && -0.13755 <= d5 <= 0.13755 && -0.14191 <= d6 <= 0.14191 && -0.3605 <= d7 <= 0.3605 && -5.2603 <= d8 <= 5.2603 && -8.8649 <= d9 <= 8.8649 && -6.3586 <= d10 <= 6.3586;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> outputinv(y->y1, y->y2, y->y3, y->y4, 1);
	 
behavior zero_input_float_model:
	 assumes d1 == 0 && d2 == 0 && d3 == 0 && d4 == 0 && d5 == 0 && d6 == 0 && d7 == 0 && d8 == 0 && d9 == 0 && d10 == 0;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> outputinv(y->y1, y->y2, y->y3, y->y4, 1 - 2 * 4 * 2.402908E-13 * 0.38 * 31.6228 - 4 * 2.402908E-13 * 4 * 2.402908E-13 * 0.38);

behavior polytope_input_float_model:
	 assumes -0.17786 <= d1 <= 0.17786 && -0.24119 <= d2 <= 0.24119 && -0.41152 <= d3 <= 0.41152 && -8.5914 <= d4 <= 8.5914 && -0.13755 <= d5 <= 0.13755 && -0.14191 <= d6 <= 0.14191 && -0.3605 <= d7 <= 0.3605 && -5.2603 <= d8 <= 5.2603 && -8.8649 <= d9 <= 8.8649 && -6.3586 <= d10 <= 6.3586;

	 ensures stateinv(\old(x->x1), \old(x->x2), \old(x->x3), \old(x->x4), \old(x->x5), \old(x->x6), \old(x->x7), \old(x->x8), \old(x->x9), \old(x->x10), \old(x->x11), \old(x->x12), \old(x->x13), \old(x->x14), \old(x->x15), \old(x->x16), 1) ==> outputinv(y->y1, y->y2, y->y3, y->y4, 1 - 2 * 4 * 2.402908E-13 * 0.38 * 31.6228 - 4 * 2.402908E-13 * 4 * 2.402908E-13 * 0.38);

*/

void updateOutput(state *x, output *y, double d1, double d2, double d3, double d4, double d5, double d6, double d7, double d8, double d9, double d10) {
	 double pre_x1 = x->x1, pre_x2 = x->x2, pre_x3 = x->x3, pre_x4 = x->x4, pre_x5 = x->x5, pre_x6 = x->x6, pre_x7 = x->x7, pre_x8 = x->x8, pre_x9 = x->x9, pre_x10 = x->x10, pre_x11 = x->x11, pre_x12 = x->x12, pre_x13 = x->x13, pre_x14 = x->x14, pre_x15 = x->x15, pre_x16 = x->x16;

	 y->y1 = -0.1168 * pre_x1 + -0.1356 * pre_x2 + 0.1307 * pre_x3 + -1.7424 * pre_x4 + -0.1123 * pre_x5 + 0.4046 * pre_x6 + -0.0082 * pre_x7 + -0.012 * pre_x8 + 0.0207 * pre_x9 + 0.4034 * pre_x10 + -0.0063 * pre_x11 + -0.0028 * pre_x12 + 0.0158 * pre_x13 + -0.004 * pre_x14 + -0.0031 * pre_x15 + -0.0047 * pre_x16 + -0.0183 * d1 + -0.0317 * d2 + -0.0094 * d3 + -0.0042 * d4 + -0.0099 * d5 + -0.1178 * d6 + -0.0166 * d7 + -0.0013 * d8 + -0.0001 * d9 + -0.0182 * d10;
	 y->y2 = 1.3036 * pre_x1 + -0.7731 * pre_x2 + -0.8455 * pre_x3 + -0.0366 * pre_x4 + 0.2469 * pre_x5 + 0.0926 * pre_x6 + -0.0655 * pre_x7 + -0.82 * pre_x8 + -0.3287 * pre_x9 + 0.0199 * pre_x10 + 0.1297 * pre_x11 + 0.007 * pre_x12 + -0.0009 * pre_x13 + 0.0151 * pre_x14 + 0.0797 * pre_x15 + -0.0078 * pre_x16 + -0.1673 * d1 + -0.0023 * d2 + -0.1095 * d3 + 0.0008 * d4 + -0.0918 * d5 + -0.0127 * d6 + -0.2402 * d7 + -0.0001 * d8 + 0.0005 * d9 + -0.0004 * d10;
	 y->y3 = -0.8852 * pre_x1 + 0.5562 * pre_x2 + -1.4662 * pre_x3 + -0.1324 * pre_x4 + 0.6282 * pre_x5 + 0.0653 * pre_x6 + 0.0461 * pre_x7 + 0.4353 * pre_x8 + -0.3534 * pre_x9 + 0.0001 * pre_x10 + -0.0726 * pre_x11 + -0.0136 * pre_x12 + 0.0007 * pre_x13 + 0 * pre_x14 + -0.0016 * pre_x15 + -0.0001 * pre_x16 + 0.0762 * d1 + -0.0018 * d2 + -0.2622 * d3 + 0.0002 * d4 + -0.1724 * d5 + -0.0196 * d6 + -0.0378 * d7 + 0.0002 * d8 + -0.0006 * d9 + 0.0005 * d10;
	 y->y4 = 0.0051 * pre_x1 + -0.0024 * pre_x2 + 0.0067 * pre_x3 + 0.0215 * pre_x4 + 0.0041 * pre_x5 + -0.0316 * pre_x6 + -0.0111 * pre_x7 + 0.0024 * pre_x8 + -0.0048 * pre_x9 + 0.0194 * pre_x10 + 0.0182 * pre_x11 + 0.03 * pre_x12 + -0.1299 * pre_x13 + -0.0087 * pre_x14 + -0.0128 * pre_x15 + -0.0737 * pre_x16 + 0.0003 * d1 + 0.0047 * d2 + 0.0067 * d3 + -0.0066 * d4 + 0.0031 * d5 + 0.0631 * d6 + 0.0244 * d7 + -0.0001 * d8 + 0 * d9 + -0.0001 * d10;

 }
