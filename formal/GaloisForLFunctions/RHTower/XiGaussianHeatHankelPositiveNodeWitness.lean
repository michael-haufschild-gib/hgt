import GaloisForLFunctions.RHTower.XiGaussianHeatHankelRealNodeWitness
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass

/-!
# Witnesses with nodes inside the spectrum

**Theorem** (`riemannHypothesis_iff_posRealNodes_heatHankel_nonneg`).  RH holds iff for every heat
time `a > 0` and every finite family of *positive* real nodes `x_i > 0`,

`Re Σ_q e^{−a w_q} ∏_i (w_q − x_i)² ≥ 0`.

Without RH a witness exists at arbitrarily large heat times
(`exists_posRealNodes_heatHankel_re_neg_of_not_riemannHypothesis`).

Every heat frequency has positive real part, `Re w_q = γ² − δ² > 0` (`re_xiHeatFrequency_pos`, from
`|γ| > 4`).  Take an off-line frequency `u` with `Im u > 0` and the pair test with `t = 1`,
`K_u · ((X − ū) + (X − u)) = 2 K_u · (X − Re u)`, whose roots are heat frequencies and `Re u`, all
in `Re > 0`.
* The pair term is `Re c₀(a)` with `c₀(a) = e^{−au} B`.  At the heat times
  `a_k = (arg B − π + 2πk)/Im u` it equals `−|c₀(a_k)|` (`heatPairCoefficient_eq_neg_norm`).
* The frequencies above `Re u + 1` cost `O(e^{−a(Re u + 1)})` (`tail_heatPairTest_le`).

So the pair test is a witness at `a_k` for every large `k`.  The real-part reduction of the
real-node witness (`re_heatHankel_split`) replaces a non-real root `r` by `Re r` or drops it.  It
keeps all roots in `Re > 0`, so the final real nodes are positive
(`exists_posRealRooted_heatHankel_re_neg_aux`).

Together with the small-time positivity of stable tests (`exists_heatHankel_re_pos_of_roots_re_nonpos`),
this places the RH content of the heat Hankel form on tests with nodes inside the spectrum.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (conjPoly)

namespace RHTower

noncomputable section

/-- Every heat frequency has positive real part: `Re w_q = γ² − δ²` with `|γ| > 4`, `δ² < ¼`. -/
theorem re_xiHeatFrequency_pos (q : XiZeroCopy) : 0 < (xiHeatFrequency q).re := by
  rw [xiHeatFrequency_re]
  have h4 := four_lt_abs_xiCopyOrdinate q
  have hre : (xiSpectralPoint q).re = xiCopyOrdinate q := by
    simp [xiSpectralPoint, xiCopyOrdinate, Complex.mul_re]
  have him := xiSpectralPoint_im_sq_lt_quarter q
  rw [hre]
  have hsq : (16 : ℝ) < xiCopyOrdinate q ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (xiCopyOrdinate q)]
  linarith

/-! ## Real-part reduction inside the right half-plane -/

/-- The real-part reduction of the real-node witness keeps every root in `Re > 0`. -/
theorem exists_posRealRooted_heatHankel_re_neg_aux {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∀ P : ℂ[X], Multiset.countP (fun z : ℂ => z.im ≠ 0) P.roots = n →
      (∀ z ∈ P.roots, 0 < z.re) → (heatHankel a P P).re < 0 →
      ∃ p : ℂ[X], p ≠ 0 ∧ (∀ z ∈ p.roots, z.im = 0 ∧ 0 < z.re) ∧ (heatHankel a p p).re < 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hpos hneg
  have hP : P ≠ 0 := by
    rintro rfl
    simp [heatHankel, heatHankelTermAt] at hneg
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exact ⟨P, hP, fun z hz => ⟨not_not.1 (Multiset.countP_eq_zero.1 hn z hz), hpos z hz⟩, hneg⟩
  obtain ⟨r, hrP, hrim⟩ := Multiset.countP_pos.1 (hn ▸ h0)
  have hr : P.IsRoot r := (mem_roots hP).1 hrP
  have hPQ := eq_mul_divByMonic_of_isRoot hr
  have hQ := divByMonic_ne_zero_of_isRoot hP hr
  set Q := P /ₘ (X - C r)
  have hQ₁ : Q * (X - C (r.re : ℂ)) ≠ 0 := mul_ne_zero hQ (X_sub_C_ne_zero _)
  have hQroots : ∀ z ∈ Q.roots, z ∈ P.roots := fun z hz => by
    rw [hPQ, roots_mul (hPQ ▸ hP)]
    exact Multiset.mem_add.2 (Or.inl hz)
  have hQpos : ∀ z ∈ Q.roots, 0 < z.re := fun z hz => hpos z (hQroots z hz)
  have hrpos : 0 < r.re := hpos r hrP
  have hQ₁pos : ∀ z ∈ (Q * (X - C (r.re : ℂ))).roots, 0 < z.re := by
    intro z hz
    rw [roots_mul hQ₁, roots_X_sub_C] at hz
    rcases Multiset.mem_add.1 hz with h | h
    · exact hQpos z h
    · rw [Multiset.mem_singleton.1 h]
      simpa using hrpos
  have hcountQ : Multiset.countP (fun z : ℂ => z.im ≠ 0) Q.roots = n - 1 := by
    have h := hn
    rw [hPQ, roots_mul (hPQ ▸ hP), roots_X_sub_C, Multiset.countP_add,
      ← Multiset.cons_zero, Multiset.countP_cons_of_pos (p := fun z : ℂ => z.im ≠ 0) _ hrim,
      Multiset.countP_zero] at h
    omega
  have hcountQ₁ :
      Multiset.countP (fun z : ℂ => z.im ≠ 0) (Q * (X - C (r.re : ℂ))).roots = n - 1 := by
    rw [roots_mul hQ₁, roots_X_sub_C, Multiset.countP_add, ← Multiset.cons_zero,
      Multiset.countP_cons_of_neg (p := fun z : ℂ => z.im ≠ 0) _ (by simp), Multiset.countP_zero,
      add_zero, hcountQ]
  have hsplit := re_heatHankel_split ha Q r
  rw [← hPQ] at hsplit
  have hlt : n - 1 < n := by omega
  by_cases h₁ : (heatHankel a (Q * (X - C (r.re : ℂ))) (Q * (X - C (r.re : ℂ)))).re < 0
  · exact ih (n - 1) hlt _ hcountQ₁ hQ₁pos h₁
  · have h₂ : (heatHankel a Q Q).re < 0 := by
      by_contra h₂
      nlinarith [mul_nonneg (sq_nonneg r.im) (not_lt.1 h₂), not_lt.1 h₁]
    exact ih (n - 1) hlt Q hcountQ hQpos h₂

/-- **Positive real nodes.**  A witness with all roots in `Re > 0` yields a witness with positive real
nodes. -/
theorem exists_posRealNodes_heatHankel_re_neg {a : ℝ} (ha : 0 < a) {P : ℂ[X]}
    (hpos : ∀ z ∈ P.roots, 0 < z.re) (h : (heatHankel a P P).re < 0) :
    ∃ s : Multiset ℝ, (∀ x ∈ s, 0 < x) ∧ (heatHankel a (realNodePoly s) (realNodePoly s)).re < 0 := by
  obtain ⟨p, -, hpr, hpneg⟩ := exists_posRealRooted_heatHankel_re_neg_aux ha _ P rfl hpos h
  refine ⟨p.roots.map Complex.re, fun x hx => ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    exact (hpr z hz).2
  have hmap : realNodePoly (p.roots.map Complex.re) = (p.roots.map fun z => X - C z).prod := by
    rw [realNodePoly, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun z hz => ?_)
    simp only [Function.comp_apply]
    congr 2
    exact Complex.ext (by simp) (by simp [(hpr z hz).1])
  have hp := (C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p))).symm
  rw [hmap]
  rw [hp, heatHankel_C_mul, re_ofReal_mul] at hpneg
  exact neg_of_mul_neg_right hpneg (Complex.normSq_nonneg _)

/-! ## The pair test at `t = 1` -/

theorem heatPairTest_one (u : ℂ) :
    heatPairTest u 1 = heatLowFrequencyKiller u * (C 2 * (X - C (u.re : ℂ))) := by
  rw [heatPairTest]
  congr 1
  have h : (starRingEnd ℂ) u + u = ((2 * u.re : ℝ) : ℂ) := by
    rw [add_comm, Complex.add_conj]
  have h2 : C (((2 * u.re : ℝ) : ℂ)) = C 2 * C (u.re : ℂ) := by
    rw [← C_mul]; push_cast; ring_nf
  calc X - C ((starRingEnd ℂ) u) + C 1 * (X - C u)
      = C 2 * X - C ((starRingEnd ℂ) u + u) := by
        rw [C_add, C_1, show (C 2 : ℂ[X]) = 2 by rfl]; ring
    _ = C 2 * (X - C (u.re : ℂ)) := by rw [h, h2]; ring

/-- The roots of the pair test at `t = 1` lie in `Re > 0`. -/
theorem re_pos_of_mem_roots_heatPairTest_one {u z : ℂ} (hu : 0 < u.re)
    (hz : z ∈ (heatPairTest u 1).roots) : 0 < z.re := by
  rw [heatPairTest_one] at hz
  have hK : heatLowFrequencyKiller u ≠ 0 := by
    rw [heatLowFrequencyKiller]
    exact Finset.prod_ne_zero_iff.2 fun w _ => X_sub_C_ne_zero w
  have hL : C (2 : ℂ) * (X - C (u.re : ℂ)) ≠ 0 :=
    mul_ne_zero (C_ne_zero.2 two_ne_zero) (X_sub_C_ne_zero _)
  rw [roots_mul (mul_ne_zero hK hL), roots_C_mul _ two_ne_zero, roots_X_sub_C] at hz
  rcases Multiset.mem_add.1 hz with h | h
  · rw [heatLowFrequencyKiller, roots_prod_X_sub_C] at h
    have hw : z ∈ heatLowFrequencies u := h
    rw [heatLowFrequencies, Finset.mem_filter, Finset.mem_image] at hw
    obtain ⟨⟨q, -, rfl⟩, -⟩ := hw
    exact re_xiHeatFrequency_pos q
  · rw [Multiset.mem_singleton.1 h]
    simpa using hu

/-- **The pair coefficient at the resonant heat times.**  With `B = c₀(0)`, at heat times `a` with
`a · Im u = arg B − π + 2πk` the pair coefficient is `−|c₀(a)|`. -/
theorem heatPairCoefficient_eq_neg_norm {u : ℂ} {a : ℝ} {k : ℕ}
    (hk : a * u.im = Complex.arg (heatPairCoefficient 0 u) - Real.pi + 2 * Real.pi * k) :
    heatPairCoefficient a u = -((‖heatPairCoefficient a u‖ : ℝ) : ℂ) := by
  set B := heatPairCoefficient 0 u with hB
  have hcoef : heatPairCoefficient a u = Complex.exp (-(a : ℂ) * u) * B := by
    rw [hB, heatPairCoefficient, heatPairCoefficient]
    simp only [ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
    ring
  have hexp : Complex.exp (-(a : ℂ) * u) =
      ((Real.exp (-(a * u.re)) : ℝ) : ℂ) * Complex.exp (((-(a * u.im)) : ℝ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  have hBpolar : B = ((‖B‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg B : ℝ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I B).symm
  have hphase : Complex.exp (((-(a * u.im)) : ℝ) * I) * Complex.exp ((Complex.arg B : ℝ) * I) = -1 := by
    rw [← Complex.exp_add, hk]
    have : ((-(Complex.arg B - Real.pi + 2 * Real.pi * k) : ℝ) : ℂ) * I + (Complex.arg B : ℝ) * I =
        (Real.pi : ℂ) * I + ((-(k : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hval : heatPairCoefficient a u = -(((Real.exp (-(a * u.re)) * ‖B‖ : ℝ)) : ℂ) := by
    rw [hcoef, hexp]
    conv_lhs => rw [hBpolar]
    calc ((Real.exp (-(a * u.re)) : ℝ) : ℂ) * Complex.exp (((-(a * u.im)) : ℝ) * I) *
          (((‖B‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg B : ℝ) * I))
        = ((Real.exp (-(a * u.re)) : ℝ) : ℂ) * ((‖B‖ : ℝ) : ℂ) *
          (Complex.exp (((-(a * u.im)) : ℝ) * I) * Complex.exp ((Complex.arg B : ℝ) * I)) := by
          ring
      _ = _ := by rw [hphase]; push_cast; ring
  have hnorm : ‖heatPairCoefficient a u‖ = Real.exp (-(a * u.re)) * ‖B‖ := by
    rw [hval, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hnorm]
  exact hval

/-- **A witness at resonant large heat times.**  For an off-line frequency `u = w_{q₀}` with
`Im u > 0`, for every `A` there is `a ≥ A` with `Re H_a(P, P) < 0` for the pair test `P` at `t = 1`. -/
theorem exists_heatHankel_re_neg_heatPairTest_one {q₀ : XiZeroCopy}
    (hq₀ : 0 < (xiHeatFrequency q₀).im) (A : ℝ) :
    ∃ a : ℝ, A ≤ a ∧ 0 < a ∧
      (heatHankel a (heatPairTest (xiHeatFrequency q₀) 1)
        (heatPairTest (xiHeatFrequency q₀) 1)).re < 0 := by
  set u := xiHeatFrequency q₀ with hu
  set D := (heatLowFrequencyKiller u).natDegree + 1
  set S₁ : ℝ := ∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * D) *
    Real.exp (-(1 * (xiHeatFrequency q).re))
  have hS₁ : 0 ≤ S₁ := tsum_nonneg fun q => by positivity
  set M : ℝ := heatPairTestMass u ^ 2 * Real.exp (u.re + 1) * S₁
  have hM0 : 0 ≤ M := by have := heatPairTestMass_nonneg u; positivity
  have hc₁ := heatPairSize_pos hq₀.ne'
  set A' := max (max 1 A) (Real.log ((M + 1) / heatPairSize u))
  set B := heatPairCoefficient 0 u
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A' * u.im + 2 * Real.pi ≤ 2 * Real.pi * k := by
    obtain ⟨k, hk⟩ := exists_nat_ge ((A' * u.im + 2 * Real.pi) / (2 * Real.pi))
    refine ⟨k, ?_⟩
    rw [div_le_iff₀ (by positivity)] at hk
    linarith
  set a := (Complex.arg B - Real.pi + 2 * Real.pi * k) / u.im
  have hak : a * u.im = Complex.arg B - Real.pi + 2 * Real.pi * k := by
    rw [div_mul_cancel₀ _ hq₀.ne']
  have haA' : A' ≤ a := by
    rw [le_div_iff₀ hq₀]
    have := Complex.neg_pi_lt_arg B
    linarith
  have ha1 : 1 ≤ a := ((le_max_left _ _).trans (le_max_left _ _)).trans haA'
  have ha : 0 < a := lt_of_lt_of_le one_pos ha1
  refine ⟨a, ((le_max_right _ _).trans (le_max_left _ _)).trans haA', ha, ?_⟩
  have hc : 0 < ‖heatPairCoefficient a u‖ := by rw [norm_heatPairCoefficient]; positivity
  have hneg := heatPairCoefficient_eq_neg_norm (u := u) hak
  have hpairq : ∀ q ∈ heatPairCopies u,
      (heatHankelTermAt a (heatPairTest u 1) (heatPairTest u 1) (xiHeatFrequency q)).re =
        -‖heatPairCoefficient a u‖ := by
    intro q hq
    have hself : (heatHankelTermAt a (heatPairTest u 1) (heatPairTest u 1) u).re =
        -‖heatPairCoefficient a u‖ := by
      rw [heatHankelTermAt_heatPairTest, map_one, mul_one, hneg]
      simp
    rcases mem_heatPairCopies.1 hq with h | h
    · rw [h, hself]
    · rw [h, heatHankelTermAt_conj, Complex.conj_re, hself]
  have hpair : ∑ q ∈ heatPairCopies u,
      (heatHankelTermAt a (heatPairTest u 1) (heatPairTest u 1) (xiHeatFrequency q)).re ≤
        -‖heatPairCoefficient a u‖ := by
    rw [Finset.sum_congr rfl hpairq, Finset.sum_const, nsmul_eq_mul]
    have hq₀F : q₀ ∈ heatPairCopies u := mem_heatPairCopies.2 (Or.inl rfl)
    have hcard : (1 : ℝ) ≤ (heatPairCopies u).card := by
      exact_mod_cast Finset.card_pos.2 ⟨q₀, hq₀F⟩
    nlinarith
  have htail := tail_heatPairTest_le ha1 (u := u) (t := 1) (by simp)
  have hlog : (M + 1) / heatPairSize u ≤ Real.exp a := by
    have h1 : Real.log ((M + 1) / heatPairSize u) ≤ a := (le_max_right _ _).trans haA'
    calc (M + 1) / heatPairSize u = Real.exp (Real.log ((M + 1) / heatPairSize u)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp a := Real.exp_le_exp.2 h1
  have hsplit : Real.exp (-(a * (u.re + 1))) = Real.exp (-(a * u.re)) * Real.exp (-a) := by
    rw [← Real.exp_add]; congr 1; ring
  have hMa : M * Real.exp (-a) < heatPairSize u := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos a)]
    rw [div_le_iff₀ hc₁] at hlog
    nlinarith
  have hexpu := Real.exp_pos (-(a * u.re))
  calc (heatHankel a (heatPairTest u 1) (heatPairTest u 1)).re
      ≤ -‖heatPairCoefficient a u‖ + M * Real.exp (-(a * (u.re + 1))) :=
        (re_heatHankel_heatPairTest_le ha).trans (add_le_add hpair htail)
    _ = Real.exp (-(a * u.re)) * (M * Real.exp (-a) - heatPairSize u) := by
        rw [norm_heatPairCoefficient, hsplit]; ring
    _ < 0 := mul_neg_of_pos_of_neg hexpu (by linarith)

/-! ## RH in positive-node form -/

/-- **Positive-node witnesses.**  Without RH, for every `A` there are a heat time `a ≥ A` and positive
real nodes `x_i > 0` with `Re Σ_q e^{−a w_q} ∏ (w_q − x_i)² < 0`. -/
theorem exists_posRealNodes_heatHankel_re_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) (A : ℝ) :
    ∃ a : ℝ, A ≤ a ∧ 0 < a ∧ ∃ s : Multiset ℝ, (∀ x ∈ s, 0 < x) ∧
      (heatHankel a (realNodePoly s) (realNodePoly s)).re < 0 := by
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis hRH
  obtain ⟨a, haA, ha, hneg⟩ := exists_heatHankel_re_neg_heatPairTest_one (q₀ := q₀) hq₀ A
  have hpos : ∀ z ∈ (heatPairTest (xiHeatFrequency q₀) 1).roots, 0 < z.re :=
    fun z hz => re_pos_of_mem_roots_heatPairTest_one (re_xiHeatFrequency_pos q₀) hz
  exact ⟨a, haA, ha, exists_posRealNodes_heatHankel_re_neg ha hpos hneg⟩

/-- **RH in positive-node form.**  RH holds iff `Re Σ_q e^{−a w_q} ∏ (w_q − x_i)² ≥ 0` for every
heat time `a > 0` and every finite family of positive real nodes. -/
theorem riemannHypothesis_iff_posRealNodes_heatHankel_nonneg :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → ∀ s : Multiset ℝ, (∀ x ∈ s, 0 < x) →
      0 ≤ (heatHankel a (realNodePoly s) (realNodePoly s)).re := by
  refine ⟨fun hRH a ha s _ => heatHankel_re_nonneg_of_riemannHypothesis ha hRH _, fun h => ?_⟩
  by_contra hRH
  obtain ⟨a, -, ha, s, hs, hneg⟩ := exists_posRealNodes_heatHankel_re_neg_of_not_riemannHypothesis hRH 0
  exact (h a ha s hs).not_gt hneg

end

end RHTower
