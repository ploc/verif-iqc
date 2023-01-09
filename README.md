# verif-iqc

## Dependencies

### Alt-Ergo with OSDP plugin
- CSDP (https://github.com/coin-or/Csdp)
- OSDP: available through opam
  - opam install osdp
- Alt-Ergo
  - install from source using the following pull-request
  - https://github.com/OCamlPro/alt-ergo/pull/499
  
  
### Frama-C v. 25.0 (Manganese) (shall work with earlier version)
  - WP plugin (installed by default)
  - https://frama-c.com/html/get-frama-c.html
  - available through opam: opam install frama-c

## Configuration

You need to declare Alt-Ergo-Poly as a prover for Why3

First run 
```
why3 config detect
```
Edit ~/.why3.conf and add:

```
[prover]
command = "alt-ergo  --polynomial-plugin osdp-plugin.cmxs --timelimit %t %f"
driver = "alt_ergo"
name = "Alt-Ergo-Poly"
version = ""
```
## Use

In examples folder, run

```
make
```

It will run the following analyses:

```
frama-c -wp -wp-model real -wp-timeout 60 -wp-prover Alt-Ergo-Poly LTI_system.c
[kernel] Parsing LTI_system.c (with preprocessing)
[kernel:parser:decimal-float] LTI_system.c:82: Warning:
  Floating-point constant 0.01 is not represented exactly. Will use 0x1.47ae147ae147bp-7.
  (warn-once: no further messages from category 'parser:decimal-float' will be emitted)
[wp] Warning: Missing RTE guards
[wp] 14 goals scheduled
[wp] Proved goals:   14 / 14
  Qed:               6  (1ms-8ms-17ms)
  Alt-Ergo-Poly :    8  (17ms-35ms) (126)


frama-c -wp -wp-model real -wp-timeout 60 -wp-prover Alt-Ergo-Poly affine_LPV_system.c
[kernel] Parsing affine_LPV_system.c (with preprocessing)
[kernel:parser:decimal-float] affine_LPV_system.c:81: Warning:
  Floating-point constant 0.01 is not represented exactly. Will use 0x1.47ae147ae147bp-7.
  (warn-once: no further messages from category 'parser:decimal-float' will be emitted)
[wp] Warning: Missing RTE guards
[wp] 14 goals scheduled
[wp] Proved goals:   14 / 14
  Qed:               6  (2ms-8ms-17ms)
  Alt-Ergo-Poly :    8  (39ms-114ms-227ms) (198)


frama-c -wp -wp-model real -wp-timeout 60 -wp-prover Alt-Ergo-Poly large_LTI_system.c
[kernel] Parsing large_LTI_system.c (with preprocessing)
[kernel:parser:decimal-float] large_LTI_system.c:109: Warning:
  Floating-point constant 0.0191 is not represented exactly. Will use 0x1.38ef34d6a161ep-6.
  (warn-once: no further messages from category 'parser:decimal-float' will be emitted)
[wp] Warning: Missing RTE guards
[wp] 28 goals scheduled
[wp] Proved goals:   28 / 28
  Qed:              20  (8ms-61ms-289ms)
  Alt-Ergo-Poly :    8  (923ms-13.4s-39.2s) (4806)
  
```

Note that the floating point errors have been computed separately. You can find the scripts and associated intermediate computations in folder lus

Files build/*.log_bounds contain the computed numerical errors
