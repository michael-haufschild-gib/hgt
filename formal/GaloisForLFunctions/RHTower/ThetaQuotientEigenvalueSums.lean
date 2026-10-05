import GaloisForLFunctions.RHTower.ThetaQuantileFourierQuotient
import GaloisForLFunctions.RHTower.XiReciprocalOrdinateLogSquare
import GaloisForLFunctions.HTGeometry.KyFanWeylSingularValues

/-!
# Modulus-ordered eigenvalue sums of the theta quotient `D`

The nonzero eigenvalues of `D = PBP` are `μ = −1/z`, `Ξ_C(z) = 0`, with algebraic multiplicity the
order of the zero; in the coordinate `ρ = 1/2 + iz` these are the Xi zeros, `|μ| = 1/|ρ − 1/2|`.
Let `Λ(N)` be the largest `Σ m(μ)|μ|` over at most `N` eigenvalues counted with algebraic
multiplicity (the modulus-ordered partial sum).

* Weyl: `Λ(N) ≤ K_N(D)`.
* `Λ(N) ≤ 2S(T) + N/T` for every `T > 0`, and `Λ(N) ≥ 2S(T) − C` whenever `2N(T) ≤ N`, where
  `S(T) = Σ_{0<γ≤T} m/γ` and `C` comes from `Σ m/|ρ − 1/2|² < ∞`.
* Hence `Λ(N) = (1/(2π) + o(1)) (log N)²`.
-/

open MeasureTheory Set Filter Topology Module

namespace RHTower

noncomputable section

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

/-! ## Symmetric supports -/

/-- Xi supports with `|γ| ≤ T`. -/
abbrev xiSupportsSym (T : ℝ) : Finset XiDivisorSupport := (xiSupportsUpTo_finite T).toFinset

theorem mem_xiSupportsSym {T : ℝ} {ρ : XiDivisorSupport} : ρ ∈ xiSupportsSym T ↔ |(ρ : ℂ).im| ≤ T := by
  rw [Set.Finite.mem_toFinset]; rfl

/-- Conjugation splits a conjugation-invariant sum over `|γ| ≤ T` into two equal halves. -/
theorem sum_xiSupportsSym_eq_two_mul {T : ℝ} (f : XiDivisorSupport → ℝ)
    (hf : ∀ ρ, f (xiSupportConj ρ) = f ρ) :
    ∑ ρ ∈ xiSupportsSym T, f ρ = 2 * ∑ ρ ∈ xiSupportsPos T, f ρ := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (xiSupportsSym T)
    (fun ρ : XiDivisorSupport => 0 < (ρ : ℂ).im) f
  have hpos : (xiSupportsSym T).filter (fun ρ : XiDivisorSupport => 0 < (ρ : ℂ).im) = xiSupportsPos T := rfl
  have hc : ∀ ρ : XiDivisorSupport, ((xiSupportConj ρ : XiDivisorSupport) : ℂ).im = -(ρ : ℂ).im := fun ρ => by
    rw [xiSupportConj_coe, Complex.conj_im]
  have hbij : ∑ ρ ∈ (xiSupportsSym T).filter (fun ρ : XiDivisorSupport => ¬ 0 < (ρ : ℂ).im), f ρ =
      ∑ ρ ∈ xiSupportsPos T, f ρ := by
    refine Finset.sum_nbij' (i := xiSupportConj) (j := xiSupportConj) ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      rw [Finset.mem_filter, mem_xiSupportsSym] at hρ
      have hneg : (ρ : ℂ).im < 0 := lt_of_le_of_ne (not_lt.mp hρ.2) (xiSupport_im_ne_zero ρ)
      rw [mem_xiSupportsPos, hc, abs_neg]
      exact ⟨hρ.1, by linarith⟩
    · intro ρ hρ
      rw [mem_xiSupportsPos] at hρ
      rw [Finset.mem_filter, mem_xiSupportsSym, hc, abs_neg]
      exact ⟨hρ.1, by linarith [hρ.2]⟩
    · intro ρ _; exact Subtype.ext (by simp [xiSupportConj_coe])
    · intro ρ _; exact Subtype.ext (by simp [xiSupportConj_coe])
    · intro ρ _; rw [hf]
  rw [← hsplit, hpos, hbij]; ring

/-! ## The centred coordinate -/

/-- `z(ρ) = −i(ρ − 1/2)`, so that `Ξ_C(z(ρ)) = ξ(ρ)`. -/
def xiCentred (ρ : ℂ) : ℂ := -Complex.I * (ρ - 1 / 2)

theorem half_add_xiCentred_mul_I (ρ : ℂ) : 1 / 2 + xiCentred ρ * Complex.I = ρ := by
  rw [xiCentred]; ring_nf; rw [Complex.I_sq]; ring

theorem XiC_xiCentred (ρ : ℂ) : XiC (xiCentred ρ) = xi ρ := by
  rw [XiC, half_add_xiCentred_mul_I]

theorem norm_xiCentred (ρ : ℂ) : ‖xiCentred ρ‖ = ‖ρ - 1 / 2‖ := by
  rw [xiCentred, norm_mul, norm_neg, Complex.norm_I, one_mul]

theorem re_xiCentred (ρ : ℂ) : (xiCentred ρ).re = ρ.im := by
  simp [xiCentred, Complex.mul_re]

theorem xiCentred_of_eq {z : ℂ} : xiCentred (1 / 2 + z * Complex.I) = z := by
  rw [xiCentred]; ring_nf; rw [Complex.I_sq]; ring

theorem analyticOrderAt_XiC_eq_xi (z : ℂ) : analyticOrderAt XiC z = analyticOrderAt xi (1 / 2 + z * Complex.I) := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 / 2 + w * Complex.I) z := by fun_prop
  have hderiv : deriv (fun w : ℂ => 1 / 2 + w * Complex.I) z = Complex.I := by
    have : HasDerivAt (fun w : ℂ => 1 / 2 + w * Complex.I) Complex.I z := by
      simpa using ((hasDerivAt_id z).mul_const Complex.I).const_add (1 / 2 : ℂ)
    exact this.deriv
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg (by rw [hderiv]; exact Complex.I_ne_zero)
  have hfun : xi ∘ (fun w : ℂ => 1 / 2 + w * Complex.I) = XiC := by funext w; rfl
  rw [hfun] at h
  exact h

/-- The eigenvalue attached to a Xi support: `μ(ρ) = −1/z(ρ)`. -/
def xiEigenvalue (ρ : ℂ) : ℂ := -(xiCentred ρ)⁻¹

theorem xiCentred_ne_zero (ρ : XiDivisorSupport) : xiCentred (ρ : ℂ) ≠ 0 := by
  intro h
  have := xi_divisor_support_ne_half ρ
  rw [xiCentred, mul_eq_zero] at h
  rcases h with h | h
  · exact Complex.I_ne_zero (neg_eq_zero.1 h)
  · exact this (sub_eq_zero.1 h)

theorem norm_xiEigenvalue (ρ : ℂ) : ‖xiEigenvalue ρ‖ = ‖ρ - 1 / 2‖⁻¹ := by
  rw [xiEigenvalue, norm_neg, norm_inv, norm_xiCentred]

/-- The support recovered from an eigenvalue: `ρ(μ) = 1/2 + (−1/μ) i`. -/
def eigenvalueSupport (μ : ℂ) : ℂ := 1 / 2 + (-μ⁻¹) * Complex.I

theorem eigenvalueSupport_xiEigenvalue (ρ : ℂ) : eigenvalueSupport (xiEigenvalue ρ) = ρ := by
  rw [eigenvalueSupport, xiEigenvalue, inv_neg, neg_neg, inv_inv, half_add_xiCentred_mul_I]

/-- Every Xi support gives an eigenvalue of `D` whose generalized eigenspace has the multiplicity. -/
theorem finrank_thetaD_xiEigenvalue (ρ : XiDivisorSupport) :
    FiniteDimensional ℂ (thetaD.maxGenEigenspace (xiEigenvalue ρ)) ∧
      finrank ℂ (thetaD.maxGenEigenspace (xiEigenvalue ρ)) = xiSupportMultiplicity ρ := by
  have hz : XiC (xiCentred ρ) = 0 := by rw [XiC_xiCentred]; exact xi_eq_zero_of_mem_divisor_support ρ
  obtain ⟨hfin, heq⟩ := finrank_maxGenEigenspace_thetaD_of_XiC_eq_zero hz
  refine ⟨hfin, ?_⟩
  rw [analyticOrderAt_XiC_eq_xi, half_add_xiCentred_mul_I] at heq
  have hm := xiSupportMultiplicity_eq_order ρ
  have hne : analyticOrderAt xi (ρ : ℂ) ≠ ⊤ := by
    intro htop
    rw [htop] at heq
    exact ENat.coe_ne_top _ heq
  have : (finrank ℂ (thetaD.maxGenEigenspace (xiEigenvalue ρ)) : ℕ∞) =
      ((analyticOrderAt xi (ρ : ℂ)).toNat : ℕ∞) := by rw [ENat.coe_toNat hne]; exact heq
  have h2 : finrank ℂ (thetaD.maxGenEigenspace (xiEigenvalue ρ)) = (analyticOrderAt xi (ρ : ℂ)).toNat := by
    exact_mod_cast this
  rw [h2]; exact_mod_cast hm.symm

theorem xiEigenvalue_ne_zero (ρ : XiDivisorSupport) : xiEigenvalue ρ ≠ 0 :=
  neg_ne_zero.2 (inv_ne_zero (xiCentred_ne_zero ρ))

theorem eigenvalueSupport_injective : Function.Injective eigenvalueSupport := by
  intro a b h
  simp only [eigenvalueSupport, add_right_inj] at h
  have := mul_right_cancel₀ Complex.I_ne_zero h
  simpa using this

theorem xiEigenvalue_injective : Function.Injective (fun ρ : XiDivisorSupport => xiEigenvalue ρ) := by
  intro a b h
  have := congrArg eigenvalueSupport h
  simp only [eigenvalueSupport_xiEigenvalue] at this
  exact Subtype.ext this

/-- The divisor value read as a natural number. -/
def xiDivisorNat (ρ : ℂ) : ℕ := Int.toNat ((MeromorphicOn.divisor xi Set.univ) ρ)

theorem xiDivisorNat_coe (ρ : XiDivisorSupport) : xiDivisorNat ρ = xiSupportMultiplicity ρ := rfl

theorem exists_pos_lt_abs_im_xiSupport : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : XiDivisorSupport, δ < |(ρ : ℂ).im| := by
  obtain ⟨δ, hδ, hδρ⟩ := exists_pos_lt_im_xiSupport
  refine ⟨δ, hδ, fun ρ => ?_⟩
  rcases lt_or_gt_of_ne (xiSupport_im_ne_zero ρ) with h | h
  · have := hδρ (xiSupportConj ρ) (by rw [xiSupportConj_coe, Complex.conj_im]; linarith)
    rw [xiSupportConj_coe, Complex.conj_im] at this
    rw [abs_of_neg h]; exact this
  · rw [abs_of_pos h]; exact hδρ ρ h

/-! ## Eigenvalue families of `D` -/

/-- An admissible family: distinct nonzero eigenvalues `μ ∈ s` taken `m(μ) ≤ dim G(D, μ)` times,
at most `N` in total. -/
def IsThetaEigenFamily (s : Finset ℂ) (m : ℂ → ℕ) (N : ℕ) : Prop :=
  (∀ μ ∈ s, μ ≠ 0 ∧ m μ ≤ finrank ℂ (thetaD.maxGenEigenspace μ)) ∧ ∑ μ ∈ s, m μ ≤ N

/-- **The modulus-ordered eigenvalue partial sum** `Λ(N) = Σ_{j ≤ N} |λ_j(D)|`: the largest
`Σ m(μ)|μ|` over at most `N` eigenvalues counted with algebraic multiplicity. -/
def thetaQuotientEigenSum (N : ℕ) : ℝ :=
  sSup {x | ∃ (s : Finset ℂ) (m : ℂ → ℕ), IsThetaEigenFamily s m N ∧ x = ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖}

/-- **Weyl's inequality for `D`**: every admissible family has `Σ m(μ)|μ| ≤ K_N(D)`. -/
theorem sum_le_kyFanSum_of_isThetaEigenFamily {s : Finset ℂ} {m : ℂ → ℕ} {N : ℕ}
    (h : IsThetaEigenFamily s m N) :
    ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ ≤ kyFanSum thetaQuotientOperator N := by
  classical
  set s' := s.filter (fun μ => m μ ≠ 0)
  have hsum : ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ = ∑ μ ∈ s', (m μ : ℝ) * ‖μ‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs with hm
    · rfl
    · push Not at hm; simp [hm]
  have hfin : ∀ μ ∈ s', FiniteDimensional ℂ (genEigen thetaQuotientOperator μ) := by
    intro μ hμ
    obtain ⟨hμs, hm⟩ := Finset.mem_filter.1 hμ
    have hle := (h.1 μ hμs).2
    exact Module.finite_of_finrank_pos (lt_of_lt_of_le (Nat.pos_of_ne_zero hm) hle)
  have hm' : ∀ μ ∈ s', m μ ≤ finrank ℂ (genEigen thetaQuotientOperator μ) :=
    fun μ hμ => (h.1 μ (Finset.mem_filter.1 hμ).1).2
  have hweyl := sum_mul_norm_le_kyFanSum isCompactOperator_thetaQuotientOperator s' m hfin hm'
  have hcount : ∑ μ ∈ s', m μ ≤ N :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _).trans h.2
  rw [hsum]
  exact hweyl.trans (kyFanSum_mono _ hcount)

theorem thetaQuotientEigenSum_set_bddAbove (N : ℕ) :
    BddAbove {x | ∃ (s : Finset ℂ) (m : ℂ → ℕ), IsThetaEigenFamily s m N ∧ x = ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖} :=
  ⟨kyFanSum thetaQuotientOperator N, fun _ ⟨_, _, h, hx⟩ => hx ▸ sum_le_kyFanSum_of_isThetaEigenFamily h⟩

theorem thetaQuotientEigenSum_set_nonempty (N : ℕ) :
    {x | ∃ (s : Finset ℂ) (m : ℂ → ℕ), IsThetaEigenFamily s m N ∧ x = ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖}.Nonempty :=
  ⟨0, ∅, fun _ => 0, ⟨by simp, by simp⟩, by simp⟩

/-- `Λ(N) ≤ K_N(D)`. -/
theorem thetaQuotientEigenSum_le_kyFanSum (N : ℕ) :
    thetaQuotientEigenSum N ≤ kyFanSum thetaQuotientOperator N :=
  csSup_le (thetaQuotientEigenSum_set_nonempty N) fun _ ⟨_, _, h, hx⟩ =>
    hx ▸ sum_le_kyFanSum_of_isThetaEigenFamily h

theorem le_thetaQuotientEigenSum {s : Finset ℂ} {m : ℂ → ℕ} {N : ℕ} (h : IsThetaEigenFamily s m N) :
    ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ ≤ thetaQuotientEigenSum N :=
  le_csSup (thetaQuotientEigenSum_set_bddAbove N) ⟨s, m, h, rfl⟩

/-! ## The two-sided bounds -/

theorem sum_xiSupportsSym_div_abs_im (T : ℝ) :
    ∑ ρ ∈ xiSupportsSym T, (xiSupportMultiplicity ρ : ℝ) / |(ρ : ℂ).im| = 2 * xiReciprocalOrdinateSum T := by
  rw [sum_xiSupportsSym_eq_two_mul (fun ρ => (xiSupportMultiplicity ρ : ℝ) / |(ρ : ℂ).im|)
    (fun ρ => by rw [xiSupportMultiplicity_conj, xiSupportConj_coe, Complex.conj_im, abs_neg]),
    xiReciprocalOrdinateSum]
  congr 1
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [mem_xiSupportsPos] at hρ
  rw [abs_of_pos hρ.2]

/-- **Upper bound**: every admissible family has `Σ m(μ)|μ| ≤ 2S(T) + N/T`. -/
theorem sum_le_of_isThetaEigenFamily {s : Finset ℂ} {m : ℂ → ℕ} {N : ℕ} (h : IsThetaEigenFamily s m N)
    {T : ℝ} (hT : 0 < T) :
    ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ ≤ 2 * xiReciprocalOrdinateSum T + N / T := by
  classical
  set sb := s.filter (fun μ => m μ ≠ 0 ∧ 1 / T ≤ ‖μ‖)
  set sr := s.filter (fun μ => ¬ (m μ ≠ 0 ∧ 1 / T ≤ ‖μ‖))
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun μ => m μ ≠ 0 ∧ 1 / T ≤ ‖μ‖)
    (fun μ => (m μ : ℝ) * ‖μ‖)
  -- the small or empty part
  have hsmall : ∑ μ ∈ sr, (m μ : ℝ) * ‖μ‖ ≤ N / T := by
    calc ∑ μ ∈ sr, (m μ : ℝ) * ‖μ‖ ≤ ∑ μ ∈ sr, (m μ : ℝ) * (1 / T) := by
          refine Finset.sum_le_sum fun μ hμ => ?_
          have hμ' := (Finset.mem_filter.1 hμ).2
          by_cases hm : m μ = 0
          · simp [hm]
          · have : ‖μ‖ < 1 / T := by
              by_contra hge; push Not at hge; exact hμ' ⟨hm, hge⟩
            exact mul_le_mul_of_nonneg_left this.le (by positivity)
      _ = (∑ μ ∈ sr, (m μ : ℝ)) / T := by rw [← Finset.sum_mul]; ring
      _ ≤ N / T := by
          refine div_le_div_of_nonneg_right ?_ hT.le
          have : ∑ μ ∈ sr, m μ ≤ N :=
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _).trans h.2
          exact_mod_cast this
  -- the big part injects into the Xi supports with `|γ| ≤ T`
  set w : ℂ → ℝ := fun ρ => (xiDivisorNat ρ : ℝ) / |ρ.im|
  have hbig_pt : ∀ μ ∈ sb, (m μ : ℝ) * ‖μ‖ ≤ w (eigenvalueSupport μ) ∧
      eigenvalueSupport μ ∈ (xiSupportsSym T).map ⟨Subtype.val, Subtype.val_injective⟩ := by
    intro μ hμ
    obtain ⟨hμs, hm, hnorm⟩ := Finset.mem_filter.1 hμ
    obtain ⟨hμ0, hmle⟩ := h.1 μ hμs
    have hne : thetaD.maxGenEigenspace μ ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hmle
      exact hm (Nat.le_zero.1 hmle)
    obtain ⟨z, hz, hμz⟩ := exists_XiC_zero_of_maxGenEigenspace_thetaD_ne_bot hμ0 hne
    have hsupp : eigenvalueSupport μ = 1 / 2 + z * Complex.I := by
      rw [eigenvalueSupport, hμz, inv_neg, neg_neg, inv_inv]
    have hxi : xi (eigenvalueSupport μ) = 0 := by rw [hsupp]; exact hz
    set rs : XiDivisorSupport := ⟨eigenvalueSupport μ, mem_xi_divisor_support_of_eq_zero hxi⟩
    have hμρ : xiEigenvalue rs = μ := by
      show -(xiCentred (eigenvalueSupport μ))⁻¹ = μ
      rw [hsupp, xiCentred_of_eq, hμz]
    obtain ⟨-, hrank⟩ := finrank_thetaD_xiEigenvalue rs
    rw [hμρ] at hrank
    have hmρ : (m μ : ℝ) ≤ xiDivisorNat (eigenvalueSupport μ) := by
      rw [show xiDivisorNat (eigenvalueSupport μ) = xiSupportMultiplicity rs from rfl, ← hrank]
      exact_mod_cast hmle
    have hnormμ : ‖μ‖ = ‖eigenvalueSupport μ - 1 / 2‖⁻¹ := by
      rw [← hμρ, norm_xiEigenvalue, eigenvalueSupport_xiEigenvalue]
    have him0 : 0 < |(eigenvalueSupport μ).im| := abs_pos.2 (xiSupport_im_ne_zero rs)
    have himle : |(eigenvalueSupport μ).im| ≤ ‖eigenvalueSupport μ - 1 / 2‖ := by
      have := Complex.abs_im_le_norm (eigenvalueSupport μ - 1 / 2)
      simpa using this
    constructor
    · show (m μ : ℝ) * ‖μ‖ ≤ (xiDivisorNat (eigenvalueSupport μ) : ℝ) / |(eigenvalueSupport μ).im|
      rw [hnormμ, div_eq_mul_inv]
      exact mul_le_mul hmρ (inv_anti₀ him0 himle) (by positivity) (by positivity)
    · rw [Finset.mem_map]
      refine ⟨rs, mem_xiSupportsSym.2 ?_, rfl⟩
      have hT' : ‖eigenvalueSupport μ - 1 / 2‖ ≤ T := by
        have h1 : ‖eigenvalueSupport μ - 1 / 2‖⁻¹ ≥ 1 / T := by rw [← hnormμ]; exact hnorm
        have hpos : 0 < ‖eigenvalueSupport μ - 1 / 2‖ := him0.trans_le himle
        rw [ge_iff_le, one_div, inv_le_inv₀ hT hpos] at h1
        exact h1
      exact himle.trans hT'
  have hbig : ∑ μ ∈ sb, (m μ : ℝ) * ‖μ‖ ≤ 2 * xiReciprocalOrdinateSum T := by
    calc ∑ μ ∈ sb, (m μ : ℝ) * ‖μ‖ ≤ ∑ μ ∈ sb, w (eigenvalueSupport μ) :=
          Finset.sum_le_sum fun μ hμ => (hbig_pt μ hμ).1
      _ = ∑ ρ ∈ sb.image eigenvalueSupport, w ρ :=
          (Finset.sum_image fun a _ b _ hab => eigenvalueSupport_injective hab).symm
      _ ≤ ∑ ρ ∈ (xiSupportsSym T).map ⟨Subtype.val, Subtype.val_injective⟩, w ρ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) fun ρ _ _ => by
            simp only [w]; positivity
          obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hρ
          exact (hbig_pt μ hμ).2
      _ = 2 * xiReciprocalOrdinateSum T := by
          rw [Finset.sum_map, ← sum_xiSupportsSym_div_abs_im]
          rfl
  rw [← hsplit]
  linarith

theorem one_div_abs_im_sub_le {δ : ℝ} (hδ : 0 < δ) (ρ : XiDivisorSupport) (hρ : δ < |(ρ : ℂ).im|) :
    1 / |(ρ : ℂ).im| - ‖(ρ : ℂ) - 1 / 2‖⁻¹ ≤ 1 / (4 * δ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 := by
  set a := |(ρ : ℂ).im|
  set b := ‖(ρ : ℂ) - 1 / 2‖
  set c := (ρ : ℂ).re - 1 / 2
  have ha : 0 < a := hδ.trans hρ
  have hstrip := xi_divisor_support_re_mem_open_unit ρ
  have hc : c ^ 2 < 1 / 4 := by simp only [c]; nlinarith [hstrip.1, hstrip.2]
  have hb2 : b ^ 2 = a ^ 2 + c ^ 2 := by
    simp only [a, b, c]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
    simp; ring
  have hab : a ≤ b := by
    have h2 : a ^ 2 ≤ b ^ 2 := by rw [hb2]; nlinarith [sq_nonneg c]
    exact (pow_le_pow_iff_left₀ ha.le (norm_nonneg _) two_ne_zero).1 h2
  have hb : 0 < b := ha.trans_le hab
  have key : (b - a) * (a + b) = c ^ 2 := by nlinarith [hb2]
  have hba : b - a ≤ 1 / (4 * b) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (b - a) * b ≤ (b - a) * (a + b) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  calc 1 / a - b⁻¹ = (b - a) / (a * b) := by field_simp
    _ ≤ (1 / (4 * b)) / (a * b) := div_le_div_of_nonneg_right hba (by positivity)
    _ = 1 / (4 * a * b ^ 2) := by field_simp
    _ ≤ 1 / (4 * δ * b ^ 2) := one_div_le_one_div_of_le (by positivity) (by nlinarith [hρ, sq_nonneg b])
    _ = 1 / (4 * δ) / b ^ 2 := by field_simp

/-- `Λ(N) ≤ 2S(T) + N/T`. -/
theorem thetaQuotientEigenSum_le {N : ℕ} {T : ℝ} (hT : 0 < T) :
    thetaQuotientEigenSum N ≤ 2 * xiReciprocalOrdinateSum T + N / T :=
  csSup_le (thetaQuotientEigenSum_set_nonempty N) fun _ ⟨_, _, h, hx⟩ => hx ▸ sum_le_of_isThetaEigenFamily h hT

/-- **Lower bound**: `Λ(N) ≥ 2S(T) − C` whenever `2N(T) ≤ N`. -/
theorem exists_le_thetaQuotientEigenSum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∀ N : ℕ, 2 * (xiZeroCount T : ℝ) ≤ N →
      2 * xiReciprocalOrdinateSum T - C ≤ thetaQuotientEigenSum N := by
  classical
  obtain ⟨δ, hδ, hδρ⟩ := exists_pos_lt_abs_im_xiSupport
  set f : XiDivisorSupport → ℝ := fun ρ => ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
    ‖(ρ : ℂ) - 1 / 2‖ ^ (2 : ℕ)
  have hfs : Summable f := xi_zero_multiplicity_centered_inv_sq_summable
  have hf0 : ∀ ρ, 0 ≤ f ρ := fun ρ => by
    have := xi_divisor_pos_on_support ρ
    simp only [f]; positivity
  have htsum0 : 0 ≤ ∑' ρ, f ρ := tsum_nonneg hf0
  refine ⟨1 / (4 * δ) * ∑' ρ, f ρ, by positivity, fun T hT N hN => ?_⟩
  set s := (xiSupportsSym T).image (fun rs : XiDivisorSupport => xiEigenvalue rs)
  set m : ℂ → ℕ := fun μ => xiDivisorNat (eigenvalueSupport μ)
  have hmρ : ∀ rs : XiDivisorSupport, m (xiEigenvalue rs) = xiSupportMultiplicity rs := fun rs => by
    simp only [m, eigenvalueSupport_xiEigenvalue]; rfl
  have hinj : Set.InjOn (fun rs : XiDivisorSupport => xiEigenvalue rs) (xiSupportsSym T : Set XiDivisorSupport) :=
    fun a _ b _ h => xiEigenvalue_injective h
  have hcount : ∑ μ ∈ s, m μ = ∑ rs ∈ xiSupportsSym T, xiSupportMultiplicity rs := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun rs _ => hmρ rs
  have hmass : ((∑ rs ∈ xiSupportsSym T, xiSupportMultiplicity rs : ℕ) : ℝ) = 2 * (xiZeroCount T : ℝ) := by
    have h1 := xiSymmetricMass_eq_support_sum hT
    have h2 := xiSymmetricMass_eq_two_mul_xiZeroCount hT
    rw [h1] at h2
    have := congrArg (fun z : ℤ => (z : ℝ)) h2
    push_cast at this ⊢
    exact this
  have hfam : IsThetaEigenFamily s m N := by
    refine ⟨fun μ hμ => ?_, ?_⟩
    · obtain ⟨rs, -, rfl⟩ := Finset.mem_image.1 hμ
      exact ⟨xiEigenvalue_ne_zero rs, by rw [hmρ, (finrank_thetaD_xiEigenvalue rs).2]⟩
    · rw [hcount]
      have : ((∑ rs ∈ xiSupportsSym T, xiSupportMultiplicity rs : ℕ) : ℝ) ≤ N := by rw [hmass]; exact hN
      exact_mod_cast this
  have hval : ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ =
      ∑ rs ∈ xiSupportsSym T, (xiSupportMultiplicity rs : ℝ) * ‖(rs : ℂ) - 1 / 2‖⁻¹ := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun rs _ => by rw [hmρ, norm_xiEigenvalue]
  have hpt : ∀ rs : XiDivisorSupport, (xiSupportMultiplicity rs : ℝ) / |(rs : ℂ).im| - 1 / (4 * δ) * f rs ≤
      (xiSupportMultiplicity rs : ℝ) * ‖(rs : ℂ) - 1 / 2‖⁻¹ := by
    intro rs
    have h := one_div_abs_im_sub_le hδ rs (hδρ rs)
    have hm0 : (0 : ℝ) ≤ xiSupportMultiplicity rs := by positivity
    have hmf : (xiSupportMultiplicity rs : ℝ) = ((MeromorphicOn.divisor xi Set.univ) (rs : ℂ) : ℝ) := by
      have hpos := xi_divisor_pos_on_support rs
      rw [xiSupportMultiplicity]
      exact_mod_cast Int.toNat_of_nonneg hpos.le
    have := mul_le_mul_of_nonneg_left h hm0
    simp only [f]
    rw [← hmf]
    calc (xiSupportMultiplicity rs : ℝ) / |(rs : ℂ).im| - 1 / (4 * δ) *
          ((xiSupportMultiplicity rs : ℝ) / ‖(rs : ℂ) - 1 / 2‖ ^ 2) =
        (xiSupportMultiplicity rs : ℝ) * ‖(rs : ℂ) - 1 / 2‖⁻¹ +
          ((xiSupportMultiplicity rs : ℝ) * (1 / |(rs : ℂ).im| - ‖(rs : ℂ) - 1 / 2‖⁻¹) -
            (xiSupportMultiplicity rs : ℝ) * (1 / (4 * δ) / ‖(rs : ℂ) - 1 / 2‖ ^ 2)) := by ring
      _ ≤ (xiSupportMultiplicity rs : ℝ) * ‖(rs : ℂ) - 1 / 2‖⁻¹ := by linarith
  have hsumf : ∑ rs ∈ xiSupportsSym T, f rs ≤ ∑' ρ, f ρ := hfs.sum_le_tsum _ fun ρ _ => hf0 ρ
  refine le_trans ?_ (le_thetaQuotientEigenSum hfam)
  rw [hval]
  calc 2 * xiReciprocalOrdinateSum T - 1 / (4 * δ) * ∑' ρ, f ρ ≤
      2 * xiReciprocalOrdinateSum T - 1 / (4 * δ) * ∑ rs ∈ xiSupportsSym T, f rs := by
        have : 0 ≤ 1 / (4 * δ) := by positivity
        nlinarith
    _ = ∑ rs ∈ xiSupportsSym T, ((xiSupportMultiplicity rs : ℝ) / |(rs : ℂ).im| - 1 / (4 * δ) * f rs) := by
        rw [Finset.sum_sub_distrib, sum_xiSupportsSym_div_abs_im, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun rs _ => hpt rs

/-! ## The asymptotic law -/

theorem tendsto_div_log_sq_atTop : Tendsto (fun x : ℝ => x / Real.log x ^ 2) atTop atTop := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ 2 / x := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have := Real.log_pos hx
    positivity
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using h, hpos⟩
  have := h2.inv_tendsto_nhdsGT_zero
  refine this.congr' ?_
  filter_upwards with x
  simp [inv_div]

/-- **The modulus-ordered eigenvalue law** `Σ_{j≤N} |λ_j(D)| = (1/(2π) + o(1)) (log N)²`. -/
theorem tendsto_thetaQuotientEigenSum_div_log_sq :
    Tendsto (fun N : ℕ => thetaQuotientEigenSum N / Real.log N ^ 2) atTop (𝓝 (1 / (2 * Real.pi))) := by
  obtain ⟨C, hC0, hC⟩ := exists_le_thetaQuotientEigenSum
  have hS := tendsto_xiReciprocalOrdinateSum_div_log_sq
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hℓ : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hNat
  have hℓ2 : Tendsto (fun N : ℕ => Real.log N ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hℓ
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- upper envelope `(2S(N) + 1)/(log N)²`
  have hup : Tendsto (fun N : ℕ => (2 * xiReciprocalOrdinateSum N + 1) / Real.log N ^ 2) atTop
      (𝓝 (1 / (2 * Real.pi))) := by
    have h1 : Tendsto (fun N : ℕ => xiReciprocalOrdinateSum N / Real.log N ^ 2) atTop (𝓝 (1 / (4 * Real.pi))) :=
      hS.comp hNat
    have h2 : Tendsto (fun N : ℕ => 1 / Real.log N ^ 2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hℓ2
    have := (h1.const_mul 2).add h2
    rw [show 2 * (1 / (4 * Real.pi)) + 0 = 1 / (2 * Real.pi) by field_simp; ring] at this
    refine this.congr' ?_
    filter_upwards with N
    ring
  -- lower envelope at `T_N = N/(log N)²`
  set TN : ℕ → ℝ := fun N => (N : ℝ) / Real.log N ^ 2
  have hTN : Tendsto TN atTop atTop := tendsto_div_log_sq_atTop.comp hNat
  have hratio : Tendsto (fun N : ℕ => Real.log (TN N) / Real.log N) atTop (𝓝 1) := by
    have hll : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hℓ
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (hll.const_mul 2)
    rw [mul_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hℓ.eventually_gt_atTop 0, hNat.eventually_gt_atTop 0] with N hN hN0
    simp only [TN]
    rw [Real.log_div hN0.ne' (by positivity), Real.log_pow]
    field_simp
    push_cast; ring
  have hlow : Tendsto (fun N : ℕ => (2 * xiReciprocalOrdinateSum (TN N) - C) / Real.log N ^ 2) atTop
      (𝓝 (1 / (2 * Real.pi))) := by
    have h1 : Tendsto (fun N : ℕ => xiReciprocalOrdinateSum (TN N) / Real.log (TN N) ^ 2) atTop
        (𝓝 (1 / (4 * Real.pi))) := hS.comp hTN
    have h2 : Tendsto (fun N : ℕ => (Real.log (TN N) / Real.log N) ^ 2) atTop (𝓝 1) := by
      simpa using hratio.pow 2
    have h3 : Tendsto (fun N : ℕ => C / Real.log N ^ 2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hℓ2
    have := ((h1.mul h2).const_mul 2).sub h3
    rw [show 2 * (1 / (4 * Real.pi) * 1) - 0 = 1 / (2 * Real.pi) by field_simp; ring] at this
    refine this.congr' ?_
    filter_upwards [hTN.eventually_gt_atTop 1, hℓ.eventually_gt_atTop 0] with N hT hN
    have hlT : 0 < Real.log (TN N) := Real.log_pos hT
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · -- the lower family is admissible eventually: `2N(T_N) ≤ N`
    obtain ⟨T₀, hT₀, hclose⟩ := exists_xiZeroCount_close 1 one_pos
    filter_upwards [hTN.eventually_ge_atTop T₀, hℓ.eventually_ge_atTop (2 * (1 / (2 * Real.pi) + 1)),
      hNat.eventually_gt_atTop 1, hℓ.eventually_gt_atTop 0] with N hT hlogN hN1 hN
    have hT0 : 0 ≤ TN N := by simp only [TN]; positivity
    have hcount : 2 * (xiZeroCount (TN N) : ℝ) ≤ N := by
      have hc := hclose (TN N) hT
      have hup := (abs_le.1 hc).2
      have hlogT : Real.log (TN N) ≤ Real.log N := by
        refine Real.log_le_log (by linarith [hT₀]) ?_
        simp only [TN]
        rw [div_le_iff₀ (by positivity)]
        have hp : 0 < 1 / (2 * Real.pi) := by positivity
        have : 1 ≤ Real.log N ^ 2 := by nlinarith
        nlinarith
      have hTlog : TN N * Real.log (TN N) ≤ N / Real.log N := by
        have hlT0 : 0 ≤ Real.log (TN N) := Real.log_nonneg (by linarith [hT₀])
        calc TN N * Real.log (TN N) ≤ TN N * Real.log N := mul_le_mul_of_nonneg_left hlogT hT0
          _ = N / Real.log N := by simp only [TN]; field_simp
      have hNlog : (1 / (2 * Real.pi) + 1) * (N / Real.log N) ≤ N / 2 := by
        have hq : (1 / (2 * Real.pi) + 1) / Real.log N ≤ 1 / 2 := by
          rw [div_le_iff₀ hN]; linarith
        calc (1 / (2 * Real.pi) + 1) * (N / Real.log N) = N * ((1 / (2 * Real.pi) + 1) / Real.log N) := by ring
          _ ≤ N * (1 / 2) := mul_le_mul_of_nonneg_left hq (by positivity)
          _ = N / 2 := by ring
      have hA : 0 ≤ 1 / (2 * Real.pi) + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hTlog hA]
    have := hC (TN N) hT0 N hcount
    exact div_le_div_of_nonneg_right this (by positivity)
  · filter_upwards [hNat.eventually_gt_atTop 0] with N hN
    have := thetaQuotientEigenSum_le (N := N) hN
    rw [div_self hN.ne'] at this
    exact div_le_div_of_nonneg_right this (by positivity)

end

end RHTower
