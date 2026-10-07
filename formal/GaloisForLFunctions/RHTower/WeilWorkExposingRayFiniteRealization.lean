import GaloisForLFunctions.RHTower.WeilWorkExposingRayUniformTruncation
import GaloisForLFunctions.RHTower.WeilWorkExposingRayTailAsymptotic
import GaloisForLFunctions.RHTower.WeilFullConeNearNullPositiveDefinite

/-!
# Exact finite realization of the literal exposing ray

For one fixed additive aperture constant C, every positive epsilon and all
sufficiently large N admit a finite nonnegative mixture of actual polar C2 tests
at aperture at most log(N)/2+C. Its full integer atom trace is exactly the
truncated exposing weight, and its archimedean energy is at most
`archimedeanExposingThreshold + (1+epsilon)*exposingTail N`.

Uniform theta-scale truncation and finite shift truncation are followed by an
exact one-atom repair at every residual integer. The positive tail lower envelope
pays all approximation errors at the natural aperture scale.

This unconditional existential upper construction does not prove the universal
matched-family lower bound required by the RH receiver.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/REALIZATION-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower.ExposingRayRealization
/-- Exact finite completion of every residual integer atom, with its full box cost. -/
theorem repair {ι : Type} [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ)
    (α : ι → ℝ) {A : ℝ} (ha : ∀ i, a i ≤ A) (hf : ∀ i, IsPolarTest (a i) (f i))
    (hα : ∀ i, 0 ≤ α i) (w : ℕ → ℝ)
    (hw : ∀ n, ⌊exp (2*A)⌋₊ < n → w n = 0) :
    ∃ (m : ℕ) (b : Fin m → ℝ) (g : Fin m → ℝ → ℂ) (β : Fin m → ℝ),
      (∀ i, b i ≤ A+1) ∧ (∀ i, IsPolarTest (b i) (g i)) ∧ (∀ i, 0 ≤ β i) ∧
      (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, β i*atomCoeff (g i) n = w n) ∧
      (∑ i, β i*archEnergy (g i)) ≤ (∑ i, α i*archEnergy (f i)) +
        ∑ n ∈ Finset.Icc 2 ⌊exp (2*A)⌋₊,
          (log n+boxConst)*|w n-2*π*∑ i, α i*atomCoeff (f i) n| := by
  classical
  let M := ⌊exp (2*A)⌋₊
  let r := fun n => w n-2*π*∑ i, α i*atomCoeff (f i) n
  let s := fun n => if 0 ≤ r n then (1:ℝ) else -1
  have hs : ∀ n, s n = 1 ∨ s n = -1 := by intro n; dsimp [s]; split_ifs <;> simp
  have hrs : ∀ n, |r n| *s n=r n := by
    intro n; dsimp [s]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  let κ := ι ⊕ ↥(Finset.Icc 2 M)
  let b : κ → ℝ := Sum.elim a (fun n => atomLevel n.1)
  let g : κ → ℝ → ℂ := Sum.elim f (fun n => twoPointResonator n.1 (s n.1))
  let β : κ → ℝ := Sum.elim α (fun n => |r n.1| /(4*π*resonatorMass n.1))
  have hb : ∀ i, b i ≤ A+1 := by
    rintro (i|n)
    · exact (ha i).trans (by linarith)
    · exact atomLevel_le (Finset.mem_Icc.mp n.2).1 (Finset.mem_Icc.mp n.2).2
  have hg : ∀ i, IsPolarTest (b i) (g i) := by
    rintro (i|n)
    · exact hf i
    · exact isPolarTest_twoPointResonator (Finset.mem_Icc.mp n.2).1 _
  have hβ : ∀ i, 0 ≤ β i := by
    rintro (i|n)
    · exact hα i
    · exact div_nonneg (abs_nonneg _) (by have := resonatorMass_pos n.1; positivity)
  have hM : ∀ i, ⌊exp (2*a i)⌋₊ ≤ M := fun i =>
    Nat.floor_mono (exp_le_exp.mpr (by linarith [ha i]))
  have hmatch : ∀ n : ℕ, 2 ≤ n → 2*π*∑ i, β i*atomCoeff (g i) n=w n := by
    intro n hn
    rw [Fintype.sum_sum_type]
    have hres : ∑ j : ↥(Finset.Icc 2 M), β (Sum.inr j)*atomCoeff (g (Sum.inr j)) n =
        ∑ j ∈ Finset.Icc 2 M, if n=j then r j/(2*π) else 0 := by
      rw [← Finset.sum_coe_sort (Finset.Icc 2 M)]
      apply Finset.sum_congr rfl
      intro j _
      have hj := (Finset.mem_Icc.mp j.2).1
      have hmass := (resonatorMass_pos j.1).ne'
      simp only [β,g,Sum.elim_inr]
      rw [atomCoeff_twoPointResonator hj _ hn]
      split_ifs
      · calc _ = (|r j.1| *s j.1)/(2*π) := by field_simp; ring
          _ = _ := by rw [hrs]
      · simp
    rw [hres,Finset.sum_ite_eq]
    change 2*π*((∑ i, α i*atomCoeff (f i) n)+
      if n ∈ Finset.Icc 2 M then r n/(2*π) else 0)=w n
    split_ifs with hnM
    · dsimp [r]; field_simp; ring
    · have hMn : M<n := by simpa [Finset.mem_Icc,hn] using hnM
      have hzero : ∑ i, α i*atomCoeff (f i) n=0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [atomCoeff_eq_zero_of_floor_lt (hf i).2.2.1 ((hM i).trans_lt hMn),mul_zero]
      rw [hzero,hw n hMn]; ring
  have hcost : (∑ i, β i*archEnergy (g i)) ≤ (∑ i, α i*archEnergy (f i))+
      ∑ n ∈ Finset.Icc 2 M, (log n+boxConst)*|r n| := by
    rw [Fintype.sum_sum_type]
    refine add_le_add (le_refl _) ?_
    rw [← Finset.sum_coe_sort (Finset.Icc 2 M)]
    apply Finset.sum_le_sum
    intro n _
    have hn := (Finset.mem_Icc.mp n.2).1
    have hmass := (resonatorMass_pos n.1).ne'
    have hpos : 0 ≤ |r n.1| /(4*π*resonatorMass n.1) := by
      have := resonatorMass_pos n.1; positivity
    have hbound := mul_le_mul_of_nonneg_left (archEnergy_twoPointResonator_le hn (hs n.1)) hpos
    exact hbound.trans_eq (by field_simp)
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ,b ∘ e.symm,g ∘ e.symm,β ∘ e.symm,
    fun i => hb _,fun i => hg _,fun i => hβ _,?_,?_⟩
  · intro n hn
    change 2*π*(∑ x, (fun i : κ => β i*atomCoeff (g i) n) (e.symm x))=w n
    rw [e.symm.sum_comp (fun i : κ => β i*atomCoeff (g i) n)]; exact hmatch n hn
  · change (∑ x, (fun i : κ => β i*archEnergy (g i)) (e.symm x)) ≤ _
    rw [e.symm.sum_comp (fun i : κ => β i*archEnergy (g i))]; exact hcost

private theorem geometric_finite_error {f g : ℕ → ℝ} {δ H : ℝ}
    (hδ : 0 ≤ δ) (hfg : ∀ k, |f k-g k| ≤ δ) (hg : ∀ k, |g k| ≤ H)
    (J : ℕ) :
    |(∑ k ∈ Finset.range J, (1/2:ℝ)^k*f k) - ∑' k : ℕ, (1/2:ℝ)^k*g k| ≤
      2*δ+2*H*(1/2:ℝ)^J := by
  have hs := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hsum : (∑' k : ℕ, (1/2:ℝ)^k)=2 := by
    rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)]; norm_num
  have hsG : Summable fun k : ℕ => (1/2:ℝ)^k*g k := by
    apply Summable.of_norm_bounded (hs.mul_right H)
    intro k
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hg k) (by positivity)
  have htail : |∑' k : ℕ, (1/2:ℝ)^(k+J)*g (k+J)| ≤ 2*H*(1/2:ℝ)^J := by
    have hb : ∀ k : ℕ, |(1/2:ℝ)^(k+J)*g (k+J)| ≤ (H*(1/2:ℝ)^J)*(1/2:ℝ)^k := by
      intro k
      rw [abs_mul,abs_of_nonneg (by positivity)]
      calc _ ≤ (1/2:ℝ)^(k+J)*H := mul_le_mul_of_nonneg_left (hg _) (by positivity)
        _ = _ := by rw [pow_add]; ring
    have hsB := hs.mul_left (H*(1/2:ℝ)^J)
    have hsabs : Summable fun k : ℕ => |(1/2:ℝ)^(k+J)*g (k+J)| := by
      apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hb hsB
    have ht := hsabs.tsum_le_tsum hb hsB
    rw [tsum_mul_left,hsum] at ht
    have ht' := norm_tsum_le_tsum_norm (f:=fun k : ℕ => (1/2:ℝ)^(k+J)*g (k+J))
      (by simpa only [Real.norm_eq_abs] using hsabs)
    simp only [Real.norm_eq_abs] at ht'
    exact ht'.trans (ht.trans_eq (by ring))
  have hfinite : |(∑ k ∈ Finset.range J,(1/2:ℝ)^k*f k)-
      ∑ k ∈ Finset.range J,(1/2:ℝ)^k*g k| ≤ 2*δ := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc (∑ k ∈ Finset.range J, |(1/2:ℝ)^k*f k-(1/2:ℝ)^k*g k|)
        ≤ ∑ k ∈ Finset.range J, (1/2:ℝ)^k*δ := by
          apply Finset.sum_le_sum; intro k _
          rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hfg k) (by positivity)
      _ = (∑ k ∈ Finset.range J,(1/2:ℝ)^k)*δ := by rw [Finset.sum_mul]
      _ ≤ 2*δ := mul_le_mul_of_nonneg_right
        ((hs.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)).trans_eq hsum) hδ
  rw [← hsG.sum_add_tsum_nat_add J]
  calc _ = |((∑ k ∈ Finset.range J,(1/2:ℝ)^k*f k)-
      ∑ k ∈ Finset.range J,(1/2:ℝ)^k*g k)-∑' k : ℕ,(1/2:ℝ)^(k+J)*g (k+J)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hfinite htail)

private def source (L : ℝ) (k : ℕ) : ℝ → ℂ :=
  fun u => (polarRiemannDifferenceReal L (1/((k:ℝ)+1)) u : ℂ)

private theorem shift_le (k : ℕ) : 1/((k:ℝ)+1) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α:=ℝ) k]

private theorem source_polar {L : ℝ} (hL : 0 ≤ L) (k : ℕ) :
    IsPolarTest (L+1) (source L k) := by
  have hc : (0:ℝ) ≤ 1/((k:ℝ)+1) := by positivity
  have hs := tsupport_polarRiemannDifference (L:=L) hc
  rw [polarRiemannDifference_eq] at hs
  obtain ⟨_,_,hd,_,hp,hm⟩ := exists_polarRiemannDifference_data L hc
  refine ⟨by linarith,hd,?_,hp,hm⟩
  exact hs.trans (Icc_subset_Icc (by linarith [shift_le k]) (by linarith [shift_le k]))

private def trace (L : ℝ) (J n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range J, (1/2:ℝ)^k*atomCoeff (source L k) n

private theorem trace_error :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (J n : ℕ), 2 ≤ n →
      |trace L J n-exposingWeight n| ≤
        C*(exp (-exp (2*(L-1)))+(1/2:ℝ)^J)/(n:ℝ)^2 := by
  obtain ⟨C,hC,herr⟩ := ExposingRayTruncation.polar_autocorr_error
  obtain ⟨D,hD,hkernel⟩ := exists_abs_polarExposingKernel_le
  refine ⟨4*C+4*D,by positivity,fun L J n hn => ?_⟩
  let g := fun k : ℕ => polarExposingKernel (1/((k:ℝ)+1)) (log n)+
    polarExposingKernel (1/((k:ℝ)+1)) (-log n)
  have hg : ∀ k, |g k| ≤ 2*D/(n:ℝ)^2 := by
    intro k
    have h1 := hkernel k (log n)
    have h2 := hkernel k (-log n)
    rw [abs_neg] at h2
    rw [exp_neg_two_abs_log_eq (by omega : 1 ≤ n)] at h1 h2
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hfg : ∀ k, |atomCoeff (source L k) n-g k| ≤
      2*C*exp (-exp (2*(L-1)))/(n:ℝ)^2 := by
    intro k
    have h1 := herr L (1/((k:ℝ)+1)) (by positivity) (shift_le k) (log n)
    have h2 := herr L (1/((k:ℝ)+1)) (by positivity) (shift_le k) (-log n)
    rw [abs_neg] at h2
    rw [exp_neg_two_abs_log_eq (by omega : 1 ≤ n)] at h1 h2
    have htest : ∀ y : ℝ, EF.weilTest (source L k) (source L k) y =
        (crossCorr (polarRiemannDifferenceReal L (1/((k:ℝ)+1)))
          (polarRiemannDifferenceReal L (1/((k:ℝ)+1))) y : ℂ) := fun y => weilTest_ofReal_eq _ y
    rw [atomCoeff,htest,htest,Complex.add_re,Complex.ofReal_re,Complex.ofReal_re]
    have heq : crossCorr (polarRiemannDifferenceReal L (1/((k:ℝ)+1)))
        (polarRiemannDifferenceReal L (1/((k:ℝ)+1))) (log n)+
        crossCorr (polarRiemannDifferenceReal L (1/((k:ℝ)+1)))
        (polarRiemannDifferenceReal L (1/((k:ℝ)+1))) (-log n)-g k =
        (crossCorr (polarRiemannDifferenceReal L (1/((k:ℝ)+1)))
        (polarRiemannDifferenceReal L (1/((k:ℝ)+1))) (log n)-
        polarExposingKernel (1/((k:ℝ)+1)) (log n))+
        (crossCorr (polarRiemannDifferenceReal L (1/((k:ℝ)+1)))
        (polarRiemannDifferenceReal L (1/((k:ℝ)+1))) (-log n)-
        polarExposingKernel (1/((k:ℝ)+1)) (-log n)) := by dsimp [g]; ring
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have h := geometric_finite_error (by positivity) hfg hg J
  change |trace L J n-exposingWeight n| ≤ _ at h
  refine h.trans ?_
  have hq : 0 ≤ (1/2:ℝ)^J := by positivity
  have he := (exp_pos (-exp (2*(L-1)))).le
  have hn2 : 0 < (n:ℝ)^2 := by positivity
  apply (le_div_iff₀ hn2).mpr
  have hr1 : (2*(2*C*exp (-exp (2*(L-1)))/(n:ℝ)^2)+
      2*(2*D/(n:ℝ)^2)*(1/2:ℝ)^J)*(n:ℝ)^2 =
      4*C*exp (-exp (2*(L-1)))+4*D*(1/2:ℝ)^J := by field_simp; ring
  rw [hr1]; nlinarith

private theorem source_energy_error :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ J : ℕ,
      (∑ k ∈ Finset.range J, (1/2:ℝ)^k*(archEnergy (source L k)/(2*π))) ≤
      archimedeanExposingThreshold+C*(exp (-exp (2*(L-1)))+(1/2:ℝ)^J) := by
  obtain ⟨C,L₀,hC,herr⟩ := ExposingRayTruncation.archimedean_error
  obtain ⟨D,hD,hkernel⟩ := exists_abs_polarExposingKernel_le
  let w := fun n => (ArithmeticFunction.vonMangoldt n:ℝ)
  have hw : Summable fun n => |w n| /(n:ℝ)^2 := by
    refine summable_vonMangoldt_div_sq.congr fun n => ?_
    simp only [w,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  let S := ∑' n : ℕ, |w n| /(n:ℝ)^2
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  let g := fun k : ℕ => atomPairing w (polarExposingKernel (1/((k:ℝ)+1)))
  have hg : ∀ k, |g k| ≤ 2*D*S := fun k => (summable_atomPairing_of_decay hw (hkernel k)).2
  have heq : (∑' k : ℕ,(1/2:ℝ)^k*g k)=archimedeanExposingThreshold := by
    rw [archimedeanExposingThreshold_eq,exposingValue,← polarExposingFunctional_eq_tsum hw]
    rfl
  refine ⟨2*C+4*D*S,L₀,by positivity,fun L hL J => ?_⟩
  have hfg := fun k : ℕ => herr L hL (1/((k:ℝ)+1)) (by positivity) (shift_le k)
  have h := geometric_finite_error (by positivity) hfg hg J
  rw [heq] at h
  have hbound := (le_abs_self _).trans h
  change (∑ k ∈ Finset.range J,(1/2:ℝ)^k*(archEnergy (source L k)/(2*π)))-
      archimedeanExposingThreshold ≤ _ at hbound
  have hq : 0 ≤ (1/2:ℝ)^J := by positivity
  have hexp := (exp_pos (-exp (2*(L-1)))).le
  nlinarith [mul_nonneg (mul_nonneg hD hS) hexp, mul_nonneg hC.le hq]

private def repairDensity (n : ℕ) : ℝ := (2*log n+boxConst)*((n:ℝ)^2)⁻¹

private theorem repairDensity_nonneg (n : ℕ) : 0 ≤ repairDensity n := by
  have := Real.log_natCast_nonneg n
  have := boxConst_nonneg
  dsimp [repairDensity]; positivity

private theorem repairDensity_summable : Summable repairDensity :=
  WeilExcess.summable_log_add_mul_inv_sq boxConst_nonneg

private theorem residual_cost {C : ℝ} (hC : 0 ≤ C) (L : ℝ) (J N M : ℕ)
    (htrace : ∀ n : ℕ, 2 ≤ n → |trace L J n-exposingWeight n| ≤
      C*(exp (-exp (2*(L-1)))+(1/2:ℝ)^J)/(n:ℝ)^2) :
    (∑ n ∈ Finset.Icc 2 M, (log n+boxConst)*|exposingWeightTrunc N n-trace L J n|) ≤
      exposingTail N+C*(exp (-exp (2*(L-1)))+(1/2:ℝ)^J)*(∑' n,repairDensity n) := by
  let T := C*(exp (-exp (2*(L-1)))+(1/2:ℝ)^J)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hb : ∀ n ∈ Finset.Icc 2 M,
      (log n+boxConst)*|exposingWeightTrunc N n-trace L J n| ≤
      (if N<n then exposingMajorant n else 0)+T*repairDensity n := by
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hl := Real.log_natCast_nonneg n
    have hw : 0 ≤ log n+boxConst := add_nonneg hl boxConst_nonneg
    have he : |exposingWeightTrunc N n-trace L J n| ≤
        (if N<n then |exposingWeight n| else 0)+|trace L J n-exposingWeight n| := by
      by_cases h : n ≤ N
      · simp only [exposingWeightTrunc,if_pos h,if_neg (not_lt.mpr h),zero_add,abs_sub_comm]
        exact le_rfl
      · simp only [exposingWeightTrunc,if_neg h,if_pos (lt_of_not_ge h),zero_sub,abs_neg]
        have ht := abs_add_le (trace L J n-exposingWeight n) (exposingWeight n)
        rw [sub_add_cancel] at ht; linarith
    have hmul := mul_le_mul_of_nonneg_left he hw
    have hd := mul_le_mul_of_nonneg_left (htrace n hn2) hw
    have hdom : (log n+boxConst)*(T/(n:ℝ)^2) ≤ T*repairDensity n := by
      dsimp [repairDensity]
      have hinv : 0 ≤ ((n:ℝ)^2)⁻¹ := by positivity
      have ht := mul_le_mul_of_nonneg_left (show log n+boxConst ≤ 2*log n+boxConst by linarith)
        (mul_nonneg hT hinv)
      calc (log n+boxConst)*(T/(n:ℝ)^2) = (T*((n:ℝ)^2)⁻¹)*(log n+boxConst) := by ring
        _ ≤ (T*((n:ℝ)^2)⁻¹)*(2*log n+boxConst) := ht
        _ = T*((2*log n+boxConst)*((n:ℝ)^2)⁻¹) := by ring
    have hhead : (log n+boxConst)*(if N<n then |exposingWeight n| else 0) =
        if N<n then exposingMajorant n else 0 := by
      split_ifs <;> simp [exposingMajorant,hn2]
    dsimp only [T] at hd hdom
    rw [mul_add,hhead] at hmul
    exact hmul.trans (add_le_add le_rfl (hd.trans hdom))
  calc _ ≤ ∑ n ∈ Finset.Icc 2 M, ((if N<n then exposingMajorant n else 0)+T*repairDensity n) :=
      Finset.sum_le_sum hb
    _ = (∑ n ∈ Finset.Icc 2 M,if N<n then exposingMajorant n else 0)+
        T*(∑ n ∈ Finset.Icc 2 M,repairDensity n) := by rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ exposingTail N+T*(∑' n,repairDensity n) := by
      apply add_le_add
      · exact (summable_exposingTail_terms N).sum_le_tsum _ (fun n _ => by
          split_ifs <;> [exact exposingMajorant_nonneg n; exact le_rfl])
      · exact mul_le_mul_of_nonneg_left (repairDensity_summable.sum_le_tsum _
          (fun n _ => repairDensity_nonneg n)) hT

/-- Exact finite realization at a prescribed source cutoff, including all residual atoms. -/
theorem at_cutoff :
    ∃ C L₀ : ℝ, 0 < C ∧ 0 ≤ L₀ ∧ ∀ (L : ℝ) (N : ℕ), L₀ ≤ L →
      N ≤ ⌊exp (2*(L+1))⌋₊ →
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ L+2) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧ (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        (∑ i, α i*archEnergy (f i)) ≤
          archimedeanExposingThreshold+exposingTail N+C*exp (-exp (2*(L-1))) := by
  classical
  obtain ⟨Ct,hCt,ht⟩ := trace_error
  obtain ⟨Ce,L₀,hCe,he⟩ := source_energy_error
  let S := ∑' n,repairDensity n
  have hS : 0 ≤ S := tsum_nonneg repairDensity_nonneg
  refine ⟨2*(Ce+Ct*S),max 0 L₀,by positivity,le_max_left _ _,fun L N hL hN => ?_⟩
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hLL : L₀ ≤ L := (le_max_right _ _).trans hL
  obtain ⟨J,hJ⟩ := exists_pow_lt_of_lt_one (exp_pos (-exp (2*(L-1))))
    (show (1/2:ℝ)<1 by norm_num)
  let α : Fin J → ℝ := fun k => (1/2:ℝ)^(k:ℕ)/(2*π)
  have hα : ∀ k, 0 ≤ α k := fun k => by dsimp [α]; positivity
  obtain ⟨m,b,g,β,hb,hg,hβ,hm,hcost⟩ := repair (fun _ : Fin J => L+1)
    (fun k => source L k) α (A:=L+1) (fun _ => le_rfl) (fun k => source_polar hL0 k)
    hα (exposingWeightTrunc N) (fun n hn => exposingWeightTrunc_eq_zero (hN.trans_lt hn))
  refine ⟨m,b,g,β,?_,hg,hβ,hm,?_⟩
  · intro i; have := hb i; linarith
  have htr : ∀ n : ℕ, 2*π*∑ k : Fin J, α k*atomCoeff (source L k) n=trace L J n := by
    intro n
    rw [Finset.mul_sum]
    calc (∑ k : Fin J, 2*π*(α k*atomCoeff (source L k) n)) =
        ∑ k : Fin J,(1/2:ℝ)^(k:ℕ)*atomCoeff (source L k) n := by
          apply Finset.sum_congr rfl; intro k _; dsimp [α]; field_simp
      _ = trace L J n := Fin.sum_univ_eq_sum_range (fun k => (1/2:ℝ)^k*atomCoeff (source L k) n) J
  have hen : (∑ k : Fin J, α k*archEnergy (source L k)) =
      ∑ k ∈ Finset.range J, (1/2:ℝ)^k*(archEnergy (source L k)/(2*π)) := by
    calc _ = ∑ k : Fin J, (1/2:ℝ)^(k:ℕ)*(archEnergy (source L k)/(2*π)) := by
          apply Finset.sum_congr rfl; intro k _; dsimp [α]; ring
      _ = _ := Fin.sum_univ_eq_sum_range (fun k => (1/2:ℝ)^k*(archEnergy (source L k)/(2*π))) J
  simp only [htr] at hcost
  rw [hen] at hcost
  have hsrc := he L hLL J
  have hres := residual_cost hCt.le L J N ⌊exp (2*(L+1))⌋₊ (ht L J)
  have hgap : 0 ≤ Ce+Ct*S := by positivity
  have hp : (Ce+Ct*S)*(1/2:ℝ)^J ≤ (Ce+Ct*S)*exp (-exp (2*(L-1))) :=
    mul_le_mul_of_nonneg_left hJ.le hgap
  dsimp [S] at hp
  nlinarith

private theorem tail_lower {r : ℝ} (hr : exposingWeightDecayRate<r) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ N : ℕ in atTop, d*exp (-(r*N)) ≤ exposingTail N := by
  obtain ⟨D,hD,hbound⟩ := exposingWeight_exponential_lower hr
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hbound
  refine ⟨log 2*D*exp (-r),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max n₀ 2)] with N hN
  have hN0 : n₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hn2 : 2 ≤ N+1 := by omega
  have hlow := hn₀ (N+1) (by omega)
  have hpos : 0 < exposingWeight (N+1) := lt_of_lt_of_le (by positivity) hlow
  have ht := (summable_exposingTail_terms N).le_tsum (N+1) (fun j _ => by
    split_ifs <;> [exact exposingMajorant_nonneg j; exact le_rfl])
  simp only [show N<N+1 by omega,if_true] at ht
  change exposingMajorant (N+1) ≤ exposingTail N at ht
  rw [exposingMajorant,if_pos hn2,abs_of_pos hpos] at ht
  have hl : log 2 ≤ log (N+1:ℕ) := Real.log_le_log (by norm_num)
    (by exact_mod_cast hn2)
  have hlog : 0 < log (2:ℝ) := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hlow hlog.le
  have heq : log 2*D*exp (-r)*exp (-(r*N)) = log 2*(D*exp (-(r*(N+1:ℕ)))) := by
    push_cast
    rw [show -(r*((N:ℝ)+1)) = -r+(-(r*(N:ℝ))) by ring,exp_add]
    ring
  rw [heq]
  exact hm.trans (ht.trans' (mul_le_mul_of_nonneg_right
    (by linarith [boxConst_nonneg]) hpos.le))

/-- Natural-aperture exact finite realization of the literal exposing ray.
This is an existential upper bound, not the universal lower bound required by RH. -/
theorem natural_aperture :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ log N/2+C) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧ (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        (∑ i, α i*archEnergy (f i)) ≤ archimedeanExposingThreshold+(1+ε)*exposingTail N := by
  obtain ⟨K,L₀,hK,_,hreal⟩ := at_cutoff
  let r := exposingWeightDecayRate+1
  let s := r+1
  have hr : exposingWeightDecayRate<r := by dsimp [r]; linarith
  have hs1 : 1<s := by dsimp [s,r]; linarith [exposingWeightDecayRate_pos]
  have hs0 : 0<s := by linarith
  let B := 1+log s/2
  have hB : 1<B := by dsimp [B]; linarith [Real.log_pos hs1]
  obtain ⟨d,hd,htail⟩ := tail_lower hr
  refine ⟨B+2,fun ε hε => ?_⟩
  obtain ⟨n₁,hn₁⟩ := exists_nat_ge (max (exp (2*(L₀-B))) (log (K/(ε*d))))
  filter_upwards [htail,eventually_ge_atTop (max n₁ 2)] with N ht hN
  have hN1 : n₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hNreal : (n₁:ℝ) ≤ N := by exact_mod_cast hN1
  have hsize : exp (2*(L₀-B)) ≤ (N:ℝ) :=
    (le_max_left _ _).trans (hn₁.trans hNreal)
  have hpaylog : log (K/(ε*d)) ≤ (N:ℝ) :=
    (le_max_right _ _).trans (hn₁.trans hNreal)
  let L := log N/2+B
  have hLL : L₀ ≤ L := by
    have h := Real.log_le_log (exp_pos _) hsize
    rw [Real.log_exp] at h
    dsimp [L]; linarith
  have hNfloor : N ≤ ⌊exp (2*(L+1))⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    calc (N:ℝ) = exp (log N) := (exp_log hNpos).symm
      _ ≤ exp (2*(L+1)) := exp_le_exp.mpr (by dsimp [L]; linarith)
  have hY : exp (2*(L-1))=s*N := by
    dsimp [L,B]
    rw [show 2*(log N/2+(1+log s/2)-1)=log N+log s by ring,
      exp_add,exp_log hNpos,exp_log hs0]
    ring
  have hpay : K*exp (-exp (2*(L-1))) ≤ ε*exposingTail N := by
    have hpos : 0<K/(ε*d) := div_pos hK (mul_pos hε hd)
    have hfrac : K/(ε*d) ≤ exp (N:ℝ) := by
      calc _ = exp (log (K/(ε*d))) := (exp_log hpos).symm
        _ ≤ _ := exp_le_exp.mpr hpaylog
    have hk := (div_le_iff₀ (mul_pos hε hd)).mp hfrac
    have hmul := mul_le_mul_of_nonneg_right hk (exp_pos (-(N:ℝ))).le
    have hcancel : exp (N:ℝ)*exp (-(N:ℝ))=1 := by rw [← exp_add]; simp
    have hbase : K*exp (-(N:ℝ)) ≤ ε*d := by
      calc _ ≤ exp (N:ℝ)*(ε*d)*exp (-(N:ℝ)) := hmul
        _ = (ε*d)*(exp (N:ℝ)*exp (-(N:ℝ))) := by ring
        _ = ε*d := by rw [hcancel,mul_one]
    have hsplit : exp (-(s*(N:ℝ)))=exp (-(N:ℝ))*exp (-(r*(N:ℝ))) := by
      rw [← exp_add]; congr 1; dsimp [s]; ring
    rw [hY,hsplit]
    calc K*(exp (-(N:ℝ))*exp (-(r*(N:ℝ)))) =
        (K*exp (-(N:ℝ)))*exp (-(r*(N:ℝ))) := by ring
      _ ≤ (ε*d)*exp (-(r*(N:ℝ))) := mul_le_mul_of_nonneg_right hbase (exp_pos _).le
      _ ≤ ε*exposingTail N := by
        calc (ε*d)*exp (-(r*(N:ℝ))) = ε*(d*exp (-(r*(N:ℝ)))) := by ring
          _ ≤ ε*exposingTail N := mul_le_mul_of_nonneg_left ht hε.le
  obtain ⟨m,a,f,α,ha,hf,hα,hm,hE⟩ := hreal L N hLL hNfloor
  refine ⟨m,a,f,α,?_,hf,hα,hm,?_⟩
  · intro i; simpa only [L,add_assoc] using ha i
  · nlinarith

end RHTower.ExposingRayRealization
