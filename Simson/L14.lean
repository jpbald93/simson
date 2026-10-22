import Simson.Bridge

/-!
# Layer 14: Mathlib-only restatement and a witness for the Wallace–Simson theorem

`l14_simson` mentions only Mathlib notions: the three feet are Mathlib's
`EuclideanGeometry.orthogonalProjection` of `p` onto `line[ℝ, b, c]`, `line[ℝ, c, a]`,
`line[ℝ, a, b]` (bridge `Simson.perpFoot_eq_orthogonalProjection`), the concyclicity hypothesis is
`EuclideanGeometry.Cospherical`, and the conclusion is `Collinear ℝ`. `l14_simson_feet` states
the same with the feet given by their **defining property** (on the line, `p - F` orthogonal to
the line's direction).

`l14w_simson` is the triangle `a = 5`, `b = 3 + 4i`, `c = -4 + 3i` on the circle `|z| = 5`, with
`p = -5i`. The triangle is non-degenerate, `p` is not a vertex, and the three feet
`-6/5 + 17/5 i`, `2 + i`, `6 - 2i` are computed and pairwise distinct.
-/

noncomputable section

namespace Simson

open Complex EuclideanGeometry
open scoped RealInnerProductSpace

/-- **Wallace–Simson theorem**, Mathlib-only statement (feet as orthogonal projections). -/
theorem l14_simson {a b c p : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hcirc : Cospherical ({a, b, c, p} : Set ℂ)) :
    Collinear ℝ ({(orthogonalProjection line[ℝ, b, c] p : ℂ),
      (orthogonalProjection line[ℝ, c, a] p : ℂ),
      (orthogonalProjection line[ℝ, a, b] p : ℂ)} : Set ℂ) := by
  simp only [← perpFoot_eq_orthogonalProjection]
  exact simson hab hbc hca hcirc

/-- **Bridge.** A point of `line[ℝ, u, v]` with `p - F ⟂ v - u` is the orthogonal projection. -/
theorem l14b_foot {p u v F : ℂ} (hF : F ∈ line[ℝ, u, v]) (hperp : inner ℝ (p - F) (v - u) = 0) :
    F = (orthogonalProjection line[ℝ, u, v] p : ℂ) := by
  symm
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨hF, ?_⟩
  rw [direction_affineSpan, vectorSpan_pair_rev, Submodule.mem_orthogonal_singleton_iff_inner_right,
    real_inner_comm]
  exact hperp

/-- **Wallace–Simson theorem**, Mathlib-only statement with the feet given by their defining
property. -/
theorem l14_simson_feet {a b c p Fa Fb Fc : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hcirc : Cospherical ({a, b, c, p} : Set ℂ))
    (hFa : Fa ∈ line[ℝ, b, c] ∧ inner ℝ (p - Fa) (c - b) = 0)
    (hFb : Fb ∈ line[ℝ, c, a] ∧ inner ℝ (p - Fb) (a - c) = 0)
    (hFc : Fc ∈ line[ℝ, a, b] ∧ inner ℝ (p - Fc) (b - a) = 0) :
    Collinear ℝ ({Fa, Fb, Fc} : Set ℂ) := by
  rw [l14b_foot hFa.1 hFa.2, l14b_foot hFb.1 hFb.2, l14b_foot hFc.1 hFc.2]
  exact l14_simson hab hbc hca hcirc

/-! ### Witness -/

theorem l14b_norm_eq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 = r ^ 2) : ‖z‖ = r := by
  rw [Complex.norm_def, Complex.normSq_apply, show z.re * z.re + z.im * z.im = r ^ 2 by
    linear_combination h]
  exact Real.sqrt_sq hr

theorem l14b_not_collinear {a b c : ℂ}
    (h : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_sub_cancel_right, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Witness for `l14_simson`: `a = 5`, `b = 3 + 4i`, `c = -4 + 3i`, `p = -5i` on `|z| = 5`. -/
theorem l14w_simson :
    ((5 : ℂ) ≠ 3 + 4 * I ∧ (3 + 4 * I : ℂ) ≠ -4 + 3 * I ∧ (-4 + 3 * I : ℂ) ≠ 5 ∧
      Cospherical ({(5 : ℂ), 3 + 4 * I, -4 + 3 * I, -5 * I} : Set ℂ)) ∧
    ¬ Collinear ℝ ({(5 : ℂ), 3 + 4 * I, -4 + 3 * I} : Set ℂ) ∧
    (-5 * I : ℂ) ≠ 5 ∧ (-5 * I : ℂ) ≠ 3 + 4 * I ∧ (-5 * I : ℂ) ≠ -4 + 3 * I ∧
    (orthogonalProjection line[ℝ, (3 + 4 * I : ℂ), -4 + 3 * I] (-5 * I) : ℂ) =
      -6 / 5 + 17 / 5 * I ∧
    (orthogonalProjection line[ℝ, (-4 + 3 * I : ℂ), 5] (-5 * I) : ℂ) = 2 + I ∧
    (orthogonalProjection line[ℝ, (5 : ℂ), 3 + 4 * I] (-5 * I) : ℂ) = 6 - 2 * I ∧
    (-6 / 5 + 17 / 5 * I : ℂ) ≠ 2 + I ∧ (2 + I : ℂ) ≠ 6 - 2 * I ∧
    (6 - 2 * I : ℂ) ≠ -6 / 5 + 17 / 5 * I ∧
    Collinear ℝ ({(orthogonalProjection line[ℝ, (3 + 4 * I : ℂ), -4 + 3 * I] (-5 * I) : ℂ),
      (orthogonalProjection line[ℝ, (-4 + 3 * I : ℂ), 5] (-5 * I) : ℂ),
      (orthogonalProjection line[ℝ, (5 : ℂ), 3 + 4 * I] (-5 * I) : ℂ)} : Set ℂ) := by
  have hyp : (5 : ℂ) ≠ 3 + 4 * I ∧ (3 + 4 * I : ℂ) ≠ -4 + 3 * I ∧ (-4 + 3 * I : ℂ) ≠ 5 ∧
      Cospherical ({(5 : ℂ), 3 + 4 * I, -4 + 3 * I, -5 * I} : Set ℂ) := by
    refine ⟨?_, ?_, ?_, ⟨0, 5, ?_⟩⟩
    · intro h; have := congrArg Complex.re h; norm_num at this
    · intro h; have := congrArg Complex.re h; norm_num at this
    · intro h; have := congrArg Complex.re h; norm_num at this
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rw [dist_zero_right]
      rcases hz with rfl | rfl | rfl | rfl <;> exact l14b_norm_eq (by norm_num) (by norm_num)
  refine ⟨hyp, l14b_not_collinear (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    l14_simson hyp.1 hyp.2.1 hyp.2.2.1 hyp.2.2.2⟩
  · intro h; have := congrArg Complex.re h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · rw [← perpFoot_eq_orthogonalProjection]
    apply Complex.ext
    · rw [perpFoot_re, footParam]; simp; norm_num
    · rw [perpFoot_im, footParam]; simp; norm_num
  · rw [← perpFoot_eq_orthogonalProjection]
    apply Complex.ext
    · rw [perpFoot_re, footParam]; simp; norm_num
    · rw [perpFoot_im, footParam]; simp; norm_num
  · rw [← perpFoot_eq_orthogonalProjection]
    apply Complex.ext
    · rw [perpFoot_re, footParam]; simp; norm_num
    · rw [perpFoot_im, footParam]; simp; norm_num
  · intro h; have := congrArg Complex.re h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this

end Simson
