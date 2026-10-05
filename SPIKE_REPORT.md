# simson — Wallace–Simson theorem (Lean 4 / Mathlib v4.33.1)

**Status: DONE.** Project jack:~/simson, library `Simson` (Basic, Identity, Main). Not pushed.

## Prior art
- Not in Mathlib (no Simson in Mathlib source / 100.yaml / 1000.yaml checked earlier).
- `gh search code "simson" language:lean`: only jjdishere/EG `Plan_files/Plan.lean` (a plan entry "SimsonLine -- Define the Simson line", no proof); others are unrelated (Assem–Simson–Skowroński citations).
- Exists in other systems' geometry corpora (e.g. GeoCoq / Isabelle geometry examples, Wu-method benchmarks); no Lean 4 formalisation found.

## Encoding
Plane = `ℂ`. `perpFoot p u v := AffineMap.lineMap u v t`, t = ⟨p-u, v-u⟩/|v-u|² (lemmas `perpFoot_mem_line`, `inner_perpFoot`: on line uv and p - foot ⟂ v - u, for u ≠ v).
`area2 x y z` = signed double area. "P on circumcircle" = `EuclideanGeometry.Cospherical {a,b,c,p}` (Mathlib; in ℂ = concyclic), or explicitly `dist · o = r` for all four.

## Headline statements
Simson/Main.lean:64
```lean
theorem simson {a b c p : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hcirc : EuclideanGeometry.Cospherical ({a, b, c, p} : Set ℂ)) :
    Collinear ℝ ({perpFoot p b c, perpFoot p c a, perpFoot p a b} : Set ℂ)
```
Simson/Main.lean:51
```lean
theorem simson_area {a b c p o : ℂ} {r : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha : dist a o = r) (hb : dist b o = r) (hc : dist c o = r) (hp : dist p o = r) :
    area2 (perpFoot p b c) (perpFoot p c a) (perpFoot p a b) = 0
```
Simson/Main.lean:74 (converse, algebraic form)
```lean
theorem area2_perpFoot_eq_zero_iff {a b c : ℂ} (p : ℂ) (habc : area2 a b c ≠ 0) :
    area2 (perpFoot p b c) (perpFoot p c a) (perpFoot p a b) = 0 ↔ concyc a b c p = 0
```
Simson/Identity.lean:43 — key identity `area2(feet) * D₁D₂D₃ = area2(a,b,c)² * concyc a b c p` (proved by `field_simp; ring`), where `concyc` is the 4×4 concyclicity determinant det[x, y, x²+y², 1].

Hypotheses: only pairwise distinct vertices (three distinct concyclic points are automatically non-collinear, so no separate nondegeneracy hypothesis is needed). No degenerate case needs separate handling: P = a vertex and right triangles are covered (proof is a polynomial identity). Converse `concyc = 0` means P on the circle through a,b,c (the `concyc ↔ on circle` link is not formalised for the converse).
Non-vacuity: `example` for triangle 1, i, −1 with p = −i; negative control `example`: p = 0 (centre) gives nonzero pedal area.

## Numerics
code/check_simson.py: 2000 random cases, on-circle max |det| = 7.5e-15; off-circle negative control min |det|/|ABC| = 0.053. code/cert.py, gen.py, gen2.py: sympy derivation of the identity (factor S² · K).

## Gate
- `lake build`: `Build completed successfully (8710 jobs).` EXIT 0; 0 warnings/errors in log.
- forbidden-token grep over Simson Simson.lean: empty.
- scratch/ax.out:
```
'Simson.simson' depends on axioms: [propext, Classical.choice, Quot.sound]
'Simson.simson_area' depends on axioms: [propext, Classical.choice, Quot.sound]
'Simson.area2_perpFoot_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Simson.area2_perpFoot_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Mirror: tarball sha256 530ae808…c769 matched both sides.

## Not done
Not linked to Mathlib's `EuclideanGeometry.orthogonalProjection` (own explicit `perpFoot`, characterised by membership + orthogonality lemmas). Geometric converse (collinear feet ⇒ P on circumcircle as `Cospherical`) only in determinant form.
