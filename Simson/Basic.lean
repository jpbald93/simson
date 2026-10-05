import Mathlib

/-!
# The Simson line (Wallace–Simson theorem)

The Euclidean plane is modelled as `ℂ`. For a point `p` and two distinct points `u v`,
`perpFoot p u v` is the foot of the perpendicular from `p` to the line `uv`
(characterised by `perpFoot_mem_line` and `inner_perpFoot`).

Main results:
* `Simson.simson_area` : signed double area of the three feet vanishes;
* `Simson.simson` : the three feet are collinear (`Collinear ℝ {…}`),
  for `A B C` pairwise distinct and `{A, B, C, P}` cospherical (i.e. concyclic).
-/

noncomputable section

namespace Simson

open Complex

/-- Parameter `t` of the foot `u + t (v - u)` of the perpendicular from `p` to line `uv`. -/
def footParam (p u v : ℂ) : ℝ :=
  ((p.re - u.re) * (v.re - u.re) + (p.im - u.im) * (v.im - u.im)) /
    ((v.re - u.re) ^ 2 + (v.im - u.im) ^ 2)

/-- Foot of the perpendicular from `p` to the line through `u` and `v`. -/
def perpFoot (p u v : ℂ) : ℂ := AffineMap.lineMap u v (footParam p u v)

/-- Signed double area of the triangle `x y z` (cross product of `y - x` and `z - x`). -/
def area2 (x y z : ℂ) : ℝ :=
  (y.re - x.re) * (z.im - x.im) - (y.im - x.im) * (z.re - x.re)

lemma perpFoot_re (p u v : ℂ) :
    (perpFoot p u v).re = u.re + footParam p u v * (v.re - u.re) := by
  simp [perpFoot, AffineMap.lineMap_apply]
  ring

lemma perpFoot_im (p u v : ℂ) :
    (perpFoot p u v).im = u.im + footParam p u v * (v.im - u.im) := by
  simp [perpFoot, AffineMap.lineMap_apply]
  ring

lemma sqD_ne_zero {u v : ℂ} (h : u ≠ v) : (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 ≠ 0 := by
  intro h0
  apply h
  apply Complex.ext <;> nlinarith [sq_nonneg (v.re - u.re), sq_nonneg (v.im - u.im)]

/-- The foot lies on the line `uv`. -/
lemma perpFoot_mem_line (p u v : ℂ) : perpFoot p u v ∈ line[ℝ, u, v] :=
  AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- `p - perpFoot p u v` is orthogonal to the direction `v - u` (for `u ≠ v`). -/
lemma inner_perpFoot {p u v : ℂ} (h : u ≠ v) :
    (p.re - (perpFoot p u v).re) * (v.re - u.re) +
      (p.im - (perpFoot p u v).im) * (v.im - u.im) = 0 := by
  have hD := sqD_ne_zero h
  rw [perpFoot_re, perpFoot_im, footParam]
  field_simp
  ring

lemma dist_sq_re_im (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

end Simson
