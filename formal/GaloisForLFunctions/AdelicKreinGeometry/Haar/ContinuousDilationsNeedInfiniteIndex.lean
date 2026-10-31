import GaloisForLFunctions.AdelicKreinGeometry.Haar.IndexPreservation

/-!
# Continuous dilations require infinite index for separable Haar carriers

Let `p` be positive definite on the rational affine group with integer successor. For every
nonidentity rational unit `q`, the Hecke height bound gives `|p(D_q)|² ≤ |q−1|`.
Thus positive rational dilations converging to one have carrier Gram matrices converging to
the identity, provided their pairwise ratios are distinct from one.

If `p + ψ ∘ slopeUnit` has a dilation reading continuous at one, the corresponding slope
Gram matrices converge to `(1 + ψ(1))J − I`. Their zero-sum hyperplanes have arbitrarily large
negative dimension. The exact carrier index law therefore forces infinite affine index.
-/

open Complex Finset Filter Topology Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry
/-- A nonzero integer numerator difference bounds the inverse rational height. -/
private theorem one_le_height_mul_dist_one (u : ℚˣ) (hu : u ≠ 1) :
    1 ≤ ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) * |((u : ℚ) : ℝ) - 1| := by
  let q : ℚ := u
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr u.ne_zero
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hdiff : q.num - (q.den : ℤ) ≠ 0 := by
    intro h
    apply hu
    apply Units.ext
    change q = 1
    rw [← Rat.num_div_den q, sub_eq_zero.mp h, Int.cast_natCast,
      div_self (by exact_mod_cast q.den_pos.ne' : (q.den : ℚ) ≠ 0)]
  have hgap : (1 : ℝ) ≤ |(q.num : ℝ) - (q.den : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hdiff)
  have hrat : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Rat.mul_den_eq_num q
  have he : (q.den : ℝ) * |(q : ℝ) - 1| = |(q.num : ℝ) - (q.den : ℝ)| := by
    calc (q.den : ℝ) * |(q : ℝ) - 1| = |(q.den : ℝ) * ((q : ℝ) - 1)| := by
           rw [abs_mul, abs_of_pos hden]
         _ = |(q.num : ℝ) - (q.den : ℝ)| := by
           congr 1
           nlinarith only [hrat]
  have hn : (1 : ℝ) ≤ q.num.natAbs := by
    exact_mod_cast (show 1 ≤ q.num.natAbs from Int.natAbs_pos.mpr hnum)
  have hheight : (q.den : ℝ) ≤ (q.num.natAbs : ℝ) * q.den := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn hden.le
  exact (he.symm ▸ hgap).trans (mul_le_mul_of_nonneg_right hheight (abs_nonneg _))

/-- The integer successor forces every nonidentity dilation coefficient to vanish at one. -/
theorem normSq_dilation_le_abs_sub_one {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (u : ℚˣ) (hu : u ≠ 1) :
    normSq (p (dilation u)) ≤ |((u : ℚ) : ℝ) - 1| := by
  have hheight : (0 : ℝ) < (u : ℚ).num.natAbs * (u : ℚ).den := by
    have hn : 0 < (u : ℚ).num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
    have hd := (u : ℚ).den_pos
    positivity
  have hb := normSq_dilation_le (isPosDefKernel_iff_isPosDefOnGroup.mp hp) hs u
  have hd := one_le_height_mul_dist_one u hu
  nlinarith only [hheight, hb, hd]

/-- Distinct positive rational units with a common limit at one. -/
private def nearIdentityUnit (N i : ℕ) : ℚˣ :=
  Units.mk0 (1 + (i : ℚ) / ((N : ℚ) + 1)) (by positivity)

private theorem nearIdentityUnit_pos (N i : ℕ) : 0 < (nearIdentityUnit N i : ℚ) := by
  simp only [nearIdentityUnit, Units.val_mk0]
  positivity

private theorem nearIdentityUnit_injective (N : ℕ) :
    Function.Injective (nearIdentityUnit N) := by
  intro i j h
  have hv := congrArg (fun v : ℚˣ => (v : ℚ)) h
  simp only [nearIdentityUnit, Units.val_mk0] at hv
  have hd : (N : ℚ) + 1 ≠ 0 := by positivity
  have hc : (i : ℚ) = (j : ℚ) := by
    field_simp at hv
    linarith only [hv]
  exact_mod_cast hc

private theorem tendsto_nearIdentityUnit (i : ℕ) :
    Tendsto (fun N : ℕ => ((nearIdentityUnit N i : ℚ) : ℝ)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [nearIdentityUnit, Units.val_mk0, Rat.cast_add, Rat.cast_one, Rat.cast_div,
    Rat.cast_natCast, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv, mul_zero, add_zero] using
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) :
      Tendsto (fun N : ℕ => 1 + (i : ℝ) * ((N : ℝ) + 1)⁻¹) atTop (𝓝 (1 + (i : ℝ) * 0)))

private theorem tendsto_dilation_zero {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (u : ℕ → ℚˣ)
    (hne : ∀ N, u N ≠ 1)
    (hu : Tendsto (fun N => ((u N : ℚ) : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun N => p (dilation (u N))) atTop (𝓝 0) := by
  have habs : Tendsto (fun N => |((u N : ℚ) : ℝ) - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hu.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [habs.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with N hN
  have hb := normSq_dilation_le_abs_sub_one hp hs (u N) (hne N)
  rw [Complex.normSq_eq_norm_sq] at hb
  rw [dist_zero_right]
  nlinarith only [hb, hN, hε, norm_nonneg (p (dilation (u N)))]

private theorem tendsto_nearIdentityRatio (a b : ℕ) :
    Tendsto (fun N => ((((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b : ℚˣ) : ℚ) : ℝ))
      atTop (𝓝 1) := by
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val, Rat.cast_mul, Rat.cast_inv,
    inv_one, mul_one] using
    ((tendsto_nearIdentityUnit a).inv₀ one_ne_zero).mul (tendsto_nearIdentityUnit b)

private theorem hermQuad_constant_sub_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (c : ι → ℂ) (hc : ∑ i, c i = 0) :
    hermQuad (Matrix.of (fun _ _ : ι => z) - 1) c = -∑ i, normSq (c i) := by
  have hv : Matrix.of (fun _ _ : ι => z) *ᵥ c = 0 := by
    ext a
    change (∑ b, z * c b) = 0
    rw [← mul_sum, hc, mul_zero]
  simp only [hermQuad, Matrix.sub_mulVec, hv, Matrix.one_mulVec, zero_sub,
    dotProduct, Pi.star_apply, Complex.star_def, Pi.neg_apply, mul_neg,
    ← Complex.normSq_eq_conj_mul_self, Complex.neg_re, Complex.re_sum, Complex.ofReal_re,
    sum_neg_distrib]

/-- Subtracting the identity from a constant matrix is negative on the zero-sum hyperplane. -/
private theorem constant_sub_one_index_lower (z : ℂ) (n : ℕ) :
    n ≤ hermNegIndex (Matrix.of (fun _ _ : Fin (n + 1) => z) - 1) := by
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
    { toFun := fun c => Fin.cons (-∑ i, c i) c
      map_add' := fun c d => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero, Pi.add_apply, sum_add_distrib, neg_add]
        · simp only [Fin.cons_succ, Pi.add_apply]
      map_smul' := fun r c => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
            ← mul_sum, mul_neg]
        · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hsum (c : Fin n → ℂ) : ∑ i, L c i = 0 := by
    change (∑ i : Fin (n + 1), Fin.cons (-∑ j, c j) c i) = 0
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, neg_add_cancel]
  have hneg (c : Fin n → ℂ) (hc : c ≠ 0) :
      hermQuad (Matrix.of (fun _ _ : Fin (n + 1) => z) - 1)
        (L c) < 0 := by
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    have hp : 0 < normSq (L c i.succ) := by
      change 0 < normSq (c i)
      exact Complex.normSq_pos.mpr hi
    have hb : normSq (L c i.succ) ≤ ∑ j, normSq (L c j) :=
      single_le_sum (fun j _ => normSq_nonneg (L c j)) (mem_univ _)
    rw [hermQuad_constant_sub_one z (L c) (hsum c)]
    linarith only [hp, hb]
  simpa only [Fintype.card_fin] using card_le_hermNegIndex_of_forall_neg _ L hneg

/-- A slope correction that makes a positive integer-successor carrier continuous has infinite index. -/
theorem negIndex_slope_eq_top_of_continuous_dilation {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) {ψ : ℚˣ → ℂ}
    (hψ : IsHermKernel ψ) {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → p (dilation u) + ψ u = f (u : ℚ)) :
    negIndex ψ = ⊤ := by
  have hf1 : f 1 = ψ 1 + 1 := by
    have h := hdil 1 (by norm_num)
    simpa only [map_one, hasIntegerSuccessor_one hs, Units.val_one, Rat.cast_one,
      add_comm] using h.symm
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of (fun _ _ => ψ 1 + 1) - 1
  have hH : H.IsHermitian := by
    have hψ1 : conj (ψ 1) = ψ 1 := by simpa only [inv_one] using (hψ 1).symm
    ext a b
    change conj (ψ 1 + 1 - (if b = a then 1 else 0)) =
      ψ 1 + 1 - (if a = b then 1 else 0)
    by_cases hab : a = b
    · simp only [hab, ite_true, add_sub_cancel_right, hψ1]
    · simp only [hab, Ne.symm hab, ite_false, sub_zero, map_add, hψ1, map_one]
  have hconv (a b : Fin (n + 1)) : Tendsto
      (fun N => (HeckeKreinToeplitz.gram ψ (fun i : Fin (n + 1) => nearIdentityUnit N i)) a b)
      atTop (𝓝 (H a b)) := by
    by_cases hab : a = b
    · subst b
      simpa only [HeckeKreinToeplitz.gram, inv_mul_cancel, H, Matrix.sub_apply, Matrix.of_apply,
        Matrix.one_apply_eq, add_sub_cancel_right] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ 1) atTop (𝓝 (ψ 1)))
    · have hne (N : ℕ) : (nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b ≠ 1 := by
        intro h
        exact hab (Fin.ext (nearIdentityUnit_injective N (inv_mul_eq_one.mp h)))
      have hpos (N : ℕ) :
          (0 : ℚ) < (((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b : ℚˣ) : ℚ) :=
        mul_pos (inv_pos.mpr (nearIdentityUnit_pos N a)) (nearIdentityUnit_pos N b)
      have hz := tendsto_dilation_zero hp hs
        (fun N => (nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b) hne
        (tendsto_nearIdentityRatio a b)
      have hfq := hf.tendsto.comp (tendsto_nearIdentityRatio a b)
      have he (N : ℕ) : ψ ((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b) =
          f (((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b : ℚˣ) : ℚ) -
            p (dilation ((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b)) := by
        have h := hdil _ (hpos N)
        exact eq_sub_of_add_eq (by simpa only [add_comm] using h)
      have hlim : Tendsto
          (fun N => ψ ((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b))
          atTop (𝓝 (ψ 1 + 1)) := by
        have h := (hfq.sub hz).congr' (Eventually.of_forall fun N => (he N).symm)
        simpa only [sub_zero, hf1] using h
      simpa only [HeckeKreinToeplitz.gram, H, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_ne hab,
        sub_zero] using hlim
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH hconv).exists
  exact (Nat.cast_le.mpr ((constant_sub_one_index_lower (ψ 1 + 1) n).trans hN)).trans
    (hermNegIndex_gram_le_negIndex ψ (fun i : Fin (n + 1) => nearIdentityUnit N i))

/-- A positive integer-successor carrier plus a slope correction has infinite index whenever
its dilation reading extends continuously at one. -/
theorem negIndex_add_slope_eq_top_of_continuous_dilation {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) {ψ : ℚˣ → ℂ}
    (hψ : IsHermKernel ψ) {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → p (dilation u) + ψ u = f (u : ℚ)) :
    negIndex (fun g => p g + ψ (slopeUnit g)) = ⊤ := by
  rw [negIndex_add_slope_of_integer_successor hp hs ψ hψ]
  exact negIndex_slope_eq_top_of_continuous_dilation hp hs hψ hf hdil

/-- Weil's spline correlation cannot be the dilation reading of a finite-index positive
integer-successor carrier with a slope correction. No Hecke support is assumed. -/
theorem negIndex_add_slope_eq_top_of_weil_dilation {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) {ψ : ℚˣ → ℂ}
    (hψ : IsHermKernel ψ)
    (hdil : ∀ u : posUnits, p (dilation u) + ψ u = ratCorr u) :
    negIndex (fun g => p g + ψ (slopeUnit g)) = ⊤ := by
  have hf : ContinuousAt (fun x : ℝ => splineCorr (-Real.log x)) 1 :=
    continuous_splineCorr.continuousAt.comp (Real.continuousAt_log one_ne_zero).neg
  exact negIndex_add_slope_eq_top_of_continuous_dilation hp hs hψ hf
    (fun u hu => hdil ⟨u, hu⟩)

#print axioms normSq_dilation_le_abs_sub_one
#print axioms negIndex_slope_eq_top_of_continuous_dilation
#print axioms negIndex_add_slope_eq_top_of_continuous_dilation
#print axioms negIndex_add_slope_eq_top_of_weil_dilation

end GaloisForLFunctions.AdelicKreinGeometry
