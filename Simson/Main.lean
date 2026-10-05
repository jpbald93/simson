import Simson.Identity

/-!
# The Wallace–Simson theorem
-/

noncomputable section

namespace Simson

open Complex

/-- Zero signed area means the first point lies on the line through the other two. -/
lemma mem_line_of_area2_eq_zero {x y z : ℂ} (hyz : y ≠ z) (h : area2 x y z = 0) :
    x ∈ line[ℝ, y, z] := by
  have hD := sqD_ne_zero hyz
  set t : ℝ := ((x.re - y.re) * (z.re - y.re) + (x.im - y.im) * (z.im - y.im)) /
    ((z.re - y.re) ^ 2 + (z.im - y.im) ^ 2) with ht
  have hx : x = AffineMap.lineMap y z t := by
    unfold area2 at h
    have k1 : (x.re - y.re) * ((z.re - y.re) ^ 2 + (z.im - y.im) ^ 2) =
        ((x.re - y.re) * (z.re - y.re) + (x.im - y.im) * (z.im - y.im)) * (z.re - y.re) := by
      linear_combination (-(z.im - y.im)) * h
    have k2 : (x.im - y.im) * ((z.re - y.re) ^ 2 + (z.im - y.im) ^ 2) =
        ((x.re - y.re) * (z.re - y.re) + (x.im - y.im) * (z.im - y.im)) * (z.im - y.im) := by
      linear_combination (z.re - y.re) * h
    apply Complex.ext
    · simp only [AffineMap.lineMap_apply_module', ht, Complex.add_re, Complex.real_smul,
        Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      linear_combination k1
    · simp only [AffineMap.lineMap_apply_module', ht, Complex.add_im, Complex.real_smul,
        Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      linear_combination k2
  rw [hx]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- Three points with zero signed area are collinear. -/
lemma collinear_of_area2_eq_zero {x y z : ℂ} (h : area2 x y z = 0) :
    Collinear ℝ ({x, y, z} : Set ℂ) := by
  by_cases hyz : y = z
  · subst hyz
    simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem]
    exact collinear_pair ℝ x y
  · exact collinear_insert_of_mem_affineSpan_pair (mem_line_of_area2_eq_zero hyz h)

/-- **Simson line, area form.** If `a b c` are pairwise distinct and `a, b, c, p` lie on a
common circle (centre `o`, radius `r`), the feet of the perpendiculars from `p` to the lines
`bc`, `ca`, `ab` span a triangle of zero signed area. -/
theorem simson_area {a b c p o : ℂ} {r : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha : dist a o = r) (hb : dist b o = r) (hc : dist c o = r) (hp : dist p o = r) :
    area2 (perpFoot p b c) (perpFoot p c a) (perpFoot p a b) = 0 := by
  have key := area2_perpFoot_mul p hab hbc hca
  rw [concyc_eq_zero_of_dist ha hb hc hp, mul_zero] at key
  have h1 := sqD_ne_zero hbc
  have h2 := sqD_ne_zero hca
  have h3 := sqD_ne_zero hab
  exact (mul_eq_zero.mp key).resolve_right (by positivity)

/-- **Wallace–Simson theorem.** For a triangle with pairwise distinct vertices `a b c` and a
point `p` such that `{a, b, c, p}` is concyclic (`Cospherical` in the plane `ℂ`), the feet of the
perpendiculars from `p` to the lines `bc`, `ca`, `ab` are collinear. -/
theorem simson {a b c p : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hcirc : EuclideanGeometry.Cospherical ({a, b, c, p} : Set ℂ)) :
    Collinear ℝ ({perpFoot p b c, perpFoot p c a, perpFoot p a b} : Set ℂ) := by
  obtain ⟨o, r, h⟩ := hcirc
  exact collinear_of_area2_eq_zero
    (simson_area hab hbc hca (h a (by simp)) (h b (by simp)) (h c (by simp)) (h p (by simp)))

/-- **Converse direction (algebraic form).** For a nondegenerate triangle (nonzero signed
area), the pedal triangle of `p` has zero signed area iff `p` satisfies the concyclicity
determinant equation with `a b c`, i.e. iff `p` lies on the circumcircle. -/
theorem area2_perpFoot_eq_zero_iff {a b c : ℂ} (p : ℂ) (habc : area2 a b c ≠ 0) :
    area2 (perpFoot p b c) (perpFoot p c a) (perpFoot p a b) = 0 ↔ concyc a b c p = 0 := by
  have hab : a ≠ b := by rintro rfl; apply habc; unfold area2; ring
  have hbc : b ≠ c := by rintro rfl; apply habc; unfold area2; ring
  have hca : c ≠ a := by rintro rfl; apply habc; unfold area2; ring
  have key := area2_perpFoot_mul p hab hbc hca
  have h1 := sqD_ne_zero hbc
  have h2 := sqD_ne_zero hca
  have h3 := sqD_ne_zero hab
  have hS : area2 a b c ^ 2 ≠ 0 := pow_ne_zero 2 habc
  constructor
  · intro h0
    rw [h0, zero_mul] at key
    exact (mul_eq_zero.mp key.symm).resolve_left hS
  · intro h0
    rw [h0, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_right (by positivity)

/-- Non-vacuity: the unit-circle triangle `1, i, -1` with `p = -i`. -/
example : Collinear ℝ ({perpFoot (-I) I (-1), perpFoot (-I) (-1) 1, perpFoot (-I) 1 I} :
    Set ℂ) := by
  have h1 : (1 : ℂ) ≠ I := by intro h; simpa using congrArg Complex.im h
  have h2 : I ≠ (-1 : ℂ) := by intro h; simpa using congrArg Complex.im h
  have h3 : (-1 : ℂ) ≠ 1 := by intro h; norm_num [Complex.ext_iff] at h
  refine simson h1 h2 h3 ⟨0, 1, ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

/-- Negative control: the centre of the unit circle is not on it, and its pedal triangle for
`1, i, -1` is genuinely nondegenerate. -/
example : area2 (perpFoot 0 I (-1)) (perpFoot 0 (-1) 1) (perpFoot 0 1 I) ≠ 0 := by
  simp only [area2, perpFoot_re, perpFoot_im, footParam]
  norm_num

end Simson
