import Simson.Main

/-!
# Definition bridges

The local definitions of the Simson development, tied to the standard Mathlib notions:

* `footParam_eq_inner` : `footParam p u v = ⟪p - u, v - u⟫ / ‖v - u‖²` (real inner product
  on `ℂ`);
* `perpFoot_eq_orthogonalProjection` : `perpFoot p u v` is Mathlib's
  `EuclideanGeometry.orthogonalProjection` of `p` onto `line[ℝ, u, v]`;
* `concyc_eq_zero_iff_cospherical` : for a nondegenerate triangle (`area2 a b c ≠ 0`),
  `concyc a b c p = 0` iff `{a, b, c, p}` is `EuclideanGeometry.Cospherical`.

(`area2` is already bridged to `Collinear` by `collinear_of_area2_eq_zero`.)
-/

noncomputable section

namespace Simson

open Complex
open scoped RealInnerProductSpace

/-- **Bridge for `footParam`.** The foot parameter is the usual projection coefficient
`⟪p - u, v - u⟫ / ‖v - u‖²`. -/
theorem footParam_eq_inner (p u v : ℂ) : footParam p u v = ⟪p - u, v - u⟫ / ‖v - u‖ ^ 2 := by
  rw [footParam, Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  congr 1 <;> ring

/-- **Bridge for `perpFoot`.** `perpFoot p u v` is the orthogonal projection of `p` onto the
line through `u` and `v` (for `u = v` both sides are `u`, so no hypothesis is needed). -/
theorem perpFoot_eq_orthogonalProjection (p u v : ℂ) : perpFoot p u v =
    (EuclideanGeometry.orthogonalProjection line[ℝ, u, v] p : ℂ) := by
  symm
  rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
  refine ⟨perpFoot_mem_line p u v, ?_⟩
  rw [direction_affineSpan, vectorSpan_pair_rev,
    Submodule.mem_orthogonal_singleton_iff_inner_right, Complex.inner]
  rcases eq_or_ne u v with rfl | h
  · simp
  have := inner_perpFoot (p := p) h
  simp only [vsub_eq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im]
  linear_combination this

/-- **Bridge for `concyc`.** For a nondegenerate triangle `a b c`, the concyclicity determinant
vanishes exactly when `a, b, c, p` lie on a common circle (Mathlib's `Cospherical`). -/
theorem concyc_eq_zero_iff_cospherical {a b c p : ℂ} (habc : area2 a b c ≠ 0) : concyc a b c p = 0
    ↔ EuclideanGeometry.Cospherical ({a, b, c, p} : Set ℂ) := by
  constructor
  · intro h0
    -- the circumcentre of `a b c`, written out
    set U : ℂ :=
      ⟨((a.re ^ 2 + a.im ^ 2) * (b.im - c.im) + (b.re ^ 2 + b.im ^ 2) * (c.im - a.im) +
          (c.re ^ 2 + c.im ^ 2) * (a.im - b.im)) / (2 * area2 a b c),
        ((a.re ^ 2 + a.im ^ 2) * (c.re - b.re) + (b.re ^ 2 + b.im ^ 2) * (a.re - c.re) +
          (c.re ^ 2 + c.im ^ 2) * (b.re - a.re)) / (2 * area2 a b c)⟩ with hU
    have hD : area2 a b c ≠ 0 := habc
    have hUre : 2 * area2 a b c * U.re = (a.re ^ 2 + a.im ^ 2) * (b.im - c.im) +
        (b.re ^ 2 + b.im ^ 2) * (c.im - a.im) + (c.re ^ 2 + c.im ^ 2) * (a.im - b.im) := by
      rw [hU]; field_simp
    have hUim : 2 * area2 a b c * U.im = (a.re ^ 2 + a.im ^ 2) * (c.re - b.re) +
        (b.re ^ 2 + b.im ^ 2) * (a.re - c.re) + (c.re ^ 2 + c.im ^ 2) * (b.re - a.re) := by
      rw [hU]; field_simp
    have key : ∀ z : ℂ,
        area2 a b c * (dist z U ^ 2 - dist a U ^ 2) = -concyc a b c z := by
      intro z
      rw [dist_sq_re_im, dist_sq_re_im]
      unfold concyc
      unfold area2 at hUre hUim ⊢
      linear_combination (-(z.re - a.re)) * hUre - (z.im - a.im) * hUim
    have hsame : ∀ z : ℂ, concyc a b c z = 0 → dist z U = dist a U := by
      intro z hz
      have k := key z
      rw [hz, neg_zero] at k
      have k' := sub_eq_zero.mp ((mul_eq_zero.mp k).resolve_left hD)
      exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp k'
    refine ⟨U, dist a U, ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · exact hsame z (by unfold concyc; ring)
    · exact hsame z (by unfold concyc; ring)
    · exact hsame z h0
  · rintro ⟨o, r, h⟩
    exact concyc_eq_zero_of_dist (h a (by simp)) (h b (by simp)) (h c (by simp)) (h p (by simp))

end Simson
