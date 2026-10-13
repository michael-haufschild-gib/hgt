import GaloisForLFunctions.RHTower.WeilLagFunctionDensityZeroExcursion

/-!
# Route JAS needs only one geometric progression of scales

**Theorem** (`exists_lag_progression_gt_exp_of_attainedTop`). If the maximal real part `β₀` of the
zeros is attained and `a < β₀ − ½`, then for every spacing `ℓ > 0` and every `M` some lag
`Φ(mℓ)`, `m ≥ 1`, exceeds `M e^{a mℓ}`. The proof is the simultaneous Dirichlet argument for an
attained top: along a sequence of `m` the top level contributes at least `(c/2) e^{mℓ(β₀−½)}` with
`c = Σ_{β = β₀} Re(1/(ρ(1−ρ))) > 0`, and the zeros below the top contribute `o(e^{mℓ(β₀−½)})`.

**Theorem** (`riemannHypothesis_iff_not_jasOffLineChain_and_jasProgressionPositive`). For every
spacing `ℓ > 0`, RH holds iff there is no off-line chain and, for some `X`, the level-one
constant-vector JAS product tests are positive on the primes of every interval `(y, y + L]` with
`y = e^{mℓ} ≥ X + 1`, `m ∈ ℕ`, `L ≥ 0`. For `ℓ = log 2` these are the dyadic scales `y = 2^m`.
"Zeros approach the line" may replace the absence of a chain
(`riemannHypothesis_iff_zerosApproachLine_and_jasProgressionPositive`).

So, once the off-line zeros have a farthest member whenever RH fails, a JAS producer needs to work
only at the scales of one geometric progression, which is a set of measure zero. At the other
extreme it may fail on any set of scales of lower density zero
(`riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_lowerDensityZero`).

**Proof.** At the scale `u = mℓ` the diagonal Bochner window bound gives
`|Φ(mℓ)| ≤ M e^{(15α/16) mℓ}`, where `α = β₀ − ½`
(`exists_abs_weilLagFunctionReal_le_exp_of_windows_except` with the exceptional set equal to the
complement of the progression). This contradicts the first
theorem with `a = 15α/16`.
-/

open Complex Filter Real Topology Set
open GaloisForLFunctions.HTGeometry (latticeClose exists_simultaneous_dirichlet)

namespace RHTower

noncomputable section

open OneSidedConfiguration BacklundConverse LindelofSparse

/-- **An attained top beats every smaller exponential along every progression.** -/
theorem exists_lag_progression_gt_exp_of_attainedTop {β₀ a : ℝ} (ha : a < β₀ - 1 / 2)
    (h : AttainedTop β₀) {ℓ : ℝ} (hℓ : 0 < ℓ) (M : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ M * Real.exp (a * ((m : ℝ) * ℓ)) < (weilLagFunction ((m : ℝ) * ℓ)).re := by
  classical
  obtain ⟨htop, hmax⟩ := h
  set c := topWeight β₀ with hcdef
  have hc : 0 < c := topWeight_pos htop
  set W := ∑' q : XiZeroCopy, ‖lagWeight q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  set T := topLevel β₀ with hTdef
  -- (1) a finite subset of the top level carrying all but `c/8` of the weight
  have hsT : Summable fun q : T => ‖lagWeight q‖ := summable_norm_lagWeight.subtype T
  have hsTre := summable_lagWeight_re_subtype T
  have htail := tendsto_tsum_compl_atTop_zero (fun q : T => ‖lagWeight q‖)
  obtain ⟨F, hF⟩ :=
    Filter.eventually_atTop.mp (htail.eventually_lt_const (by linarith : (0 : ℝ) < c / 8))
  have hFtail : ∑' q : {x : T // x ∉ F}, ‖lagWeight q‖ < c / 8 := hF F le_rfl
  -- (2) the resolution of the simultaneous approximation
  set Q : ℕ := ⌈16 * π * W / c⌉₊ + 1 with hQdef
  have hQ0 : 0 < Q := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQge : 16 * π * W / c ≤ Q := by
    have := Nat.le_ceil (16 * π * W / c); rw [hQdef]; push_cast; linarith
  have hQW : W * (2 * π / Q) ≤ c / 8 := by
    rw [← mul_div_assoc, div_le_iff₀ hQpos]
    have := (div_le_iff₀ hc).mp hQge
    nlinarith [Real.pi_pos]
  -- (3) the scale `N`: the lower tail is below `c/8` and the top modulus beats `M`
  set r₂ := Real.exp (ℓ * (β₀ - 1 / 2)) with hr₂
  set r₃ := Real.exp (ℓ * (β₀ - 1 / 2 - a)) with hr₃
  set rₐ := Real.exp (ℓ * a) with hrₐ
  have hr₃1 : 1 < r₃ := Real.one_lt_exp_iff.mpr (mul_pos hℓ (by linarith))
  have hr₂₃ : r₂ = rₐ * r₃ := by rw [hr₂, hr₃, hrₐ, ← Real.exp_add]; congr 1; ring
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_lowerTail hℓ hmax).eventually (eventually_le_nhds (by linarith : (0 : ℝ) < c / 8)))
  obtain ⟨N₂, hN₂⟩ := pow_unbounded_of_one_lt (2 * max M 0 / c) hr₃1
  set N := max N₁ N₂ + 1 with hNdef
  have hN0 : 0 < N := by omega
  -- (4) Dirichlet on the scaled top-level frequencies
  let e := F.equivFin
  let β : Fin F.card → ℝ := fun i => N * zeroOrdinate (e.symm i).1 * ℓ / (2 * π)
  obtain ⟨m', hm'1, -, hclose⟩ := exists_simultaneous_dirichlet β hQ0
  set m := N * m' with hmdef
  have hmN : N ≤ m := by rw [hmdef]; exact Nat.le_mul_of_pos_right N hm'1
  refine ⟨m, by omega, ?_⟩
  set L : ℝ := m * ℓ with hLdef
  have hL0 : 0 ≤ L := by positivity
  -- the phases on `F`
  have hphase : ∀ q ∈ F,
      ‖Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1‖ ≤ 2 * π / Q := by
    intro q hq
    have hc' := hclose (e ⟨q, hq⟩)
    have hβ' : β (e ⟨q, hq⟩) = N * zeroOrdinate q.1 * ℓ / (2 * π) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ'] at hc'
    have := norm_exp_phase_sub_one_le (ℓ := ℓ) (N := N) (m' := m') hc'
    rw [hLdef, hmdef]
    have e' : (((N * m' : ℕ) : ℝ) * ℓ * zeroOrdinate q.1 : ℝ)
        = ((N * m' : ℕ) : ℝ) * ℓ * zeroOrdinate q.1 := rfl
    convert this using 4
  -- (5) the value as a top part plus a lower part
  set f : XiZeroCopy → ℂ := fun q => lagWeight q * Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) with hfdef
  have hf : Summable f := summable_lagWeight_mul_exp L
  have hval : (weilLagFunction ((m : ℝ) * ℓ)).re = (∑' q : T, f q).re + (∑' q : ↑Tᶜ, f q).re := by
    rw [weilLagFunction_eq_tsum_lagWeight, ← hLdef,
      ← hf.tsum_subtype_add_tsum_subtype_compl T, Complex.add_re]
  -- top part
  set g : T → ℂ := fun q => lagWeight q * Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ))
    with hgdef
  have hg : Summable g := by
    refine (summable_norm_lagWeight.subtype T).of_norm_bounded fun q => ?_
    rw [hgdef]; simp only [norm_mul]
    rw [Complex.norm_exp]
    simp
  have hgre : Summable fun q : T => (g q).re :=
    hg.norm.of_norm_bounded fun q => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have htopval : (∑' q : T, f q).re = Real.exp (L * (β₀ - 1 / 2)) * ∑' q : T, (g q).re := by
    have e1 : ∀ q : T, f q = (Real.exp (L * (β₀ - 1 / 2)) : ℂ) * g q := by
      intro q
      have hq : ((q.1).1 : ℂ).re = β₀ := q.2
      simp only [hfdef, hgdef]
      rw [exp_lag_top hq]; ring
    rw [tsum_congr e1, tsum_mul_left, Complex.re_ofReal_mul, Complex.re_tsum hg]
  -- the top sum is at least `5c/8`
  have hgnorm : ∀ q : T, ‖g q‖ = ‖lagWeight q‖ := by
    intro q; rw [hgdef]; simp only [norm_mul]; rw [Complex.norm_exp]; simp
  have hgF : ∀ q ∈ F, (lagWeight q).re - ‖lagWeight q‖ * (2 * π / Q) ≤ (g q).re := by
    intro q hq
    have hsplit : g q = lagWeight q +
        lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1) := by
      rw [hgdef]; ring
    rw [hsplit, Complex.add_re]
    have h1 : -(‖lagWeight q‖ * (2 * π / Q))
        ≤ (lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1)).re := by
      have := neg_le_of_abs_le (Complex.abs_re_le_norm
        (lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1)))
      rw [norm_mul] at this
      have h2 := mul_le_mul_of_nonneg_left (hphase q hq) (norm_nonneg (lagWeight q))
      linarith
    linarith
  have hsplitT := hgre.sum_add_tsum_compl (s := F)
  have hsplitW := hsTre.sum_add_tsum_compl (s := F)
  have hFnorm : ∑ q ∈ F, ‖lagWeight q‖ ≤ W := by
    calc ∑ q ∈ F, ‖lagWeight q‖ ≤ ∑' q : T, ‖lagWeight q‖ :=
          hsT.sum_le_tsum F fun q _ => norm_nonneg _
      _ ≤ W := by
          rw [hWdef]
          exact Summable.tsum_subtype_le (fun q => ‖lagWeight q‖) T (fun q => norm_nonneg _)
            summable_norm_lagWeight
  have hFre : c - c / 8 ≤ ∑ q ∈ F, (lagWeight q).re := by
    have hre_le : ∑' q : {x : T // x ∉ F}, (lagWeight q).re ≤
        ∑' q : {x : T // x ∉ F}, ‖lagWeight q‖ :=
      Summable.tsum_le_tsum (fun q => Complex.re_le_norm _) (hsTre.subtype _) (hsT.subtype _)
    have e' : ∑' q : ↑(↑F : Set T)ᶜ, (lagWeight q).re =
        ∑' q : {x : T // x ∉ F}, (lagWeight q).re := rfl
    have hcval : c = ∑' q : T, (lagWeight q).re := rfl
    linarith
  have hFg : ∑ q ∈ F, (lagWeight q).re - c / 8 ≤ ∑ q ∈ F, (g q).re := by
    have h1 : ∑ q ∈ F, ((lagWeight q).re - ‖lagWeight q‖ * (2 * π / Q)) ≤ ∑ q ∈ F, (g q).re :=
      Finset.sum_le_sum hgF
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at h1
    have h2 : (∑ q ∈ F, ‖lagWeight q‖) * (2 * π / Q) ≤ W * (2 * π / Q) :=
      mul_le_mul_of_nonneg_right hFnorm (by positivity)
    linarith
  have hgtail : |∑' q : {x : T // x ∉ F}, (g q).re| ≤ c / 8 := by
    have h1 : |∑' q : ↑(↑F : Set T)ᶜ, (g q).re| ≤ ∑' q : ↑(↑F : Set T)ᶜ, ‖(g q).re‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_tsum_le_tsum_norm (hgre.norm.subtype _)
    have h2 : ∑' q : ↑(↑F : Set T)ᶜ, ‖(g q).re‖ ≤ ∑' q : ↑(↑F : Set T)ᶜ, ‖lagWeight q‖ := by
      refine Summable.tsum_le_tsum (fun q => ?_) (hgre.norm.subtype _) (hsT.subtype _)
      rw [← hgnorm q, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
    have e' : ∑' q : ↑(↑F : Set T)ᶜ, ‖lagWeight q‖ = ∑' q : {x : T // x ∉ F}, ‖lagWeight q‖ := rfl
    have e'' : ∑' q : ↑(↑F : Set T)ᶜ, (g q).re = ∑' q : {x : T // x ∉ F}, (g q).re := rfl
    rw [← e'']
    linarith
  have htopge : 5 * c / 8 ≤ ∑' q : T, (g q).re := by
    have e'' : ∑' q : ↑(↑F : Set T)ᶜ, (g q).re = ∑' q : {x : T // x ∉ F}, (g q).re := rfl
    have := (abs_le.mp hgtail).1
    linarith
  -- lower part
  have hlow : |(∑' q : ↑Tᶜ, f q).re| ≤ Real.exp (L * (β₀ - 1 / 2)) * lowerTail β₀ ℓ m :=
    abs_re_lowerPart_le β₀ ℓ m
  -- (6) the numerics
  have hexp2 : Real.exp (L * (β₀ - 1 / 2)) = r₂ ^ m := by
    rw [hr₂, ← Real.exp_nat_mul, hLdef]; congr 1; ring
  have hr₃m : 2 * max M 0 / c < r₃ ^ m := by
    calc 2 * max M 0 / c < r₃ ^ N₂ := hN₂
      _ ≤ r₃ ^ m := pow_le_pow_right₀ hr₃1.le (by omega)
  have htailm : lowerTail β₀ ℓ m ≤ c / 8 := hN₁ m (by omega)
  have hrₐpos : 0 < rₐ ^ m := by positivity
  have hexpa : Real.exp (a * ((m : ℝ) * ℓ)) = rₐ ^ m := by
    rw [hrₐ, ← Real.exp_nat_mul]; congr 1; ring
  have hMr : M * Real.exp (a * ((m : ℝ) * ℓ)) < c / 2 * r₂ ^ m := by
    have h1 := (div_lt_iff₀ hc).mp hr₃m
    have h2 : max M 0 < c / 2 * r₃ ^ m := by linarith
    rw [hexpa, hr₂₃, mul_pow]
    calc M * rₐ ^ m ≤ max M 0 * rₐ ^ m := mul_le_mul_of_nonneg_right (le_max_left _ _) hrₐpos.le
      _ < c / 2 * r₃ ^ m * rₐ ^ m := mul_lt_mul_of_pos_right h2 hrₐpos
      _ = c / 2 * (rₐ ^ m * r₃ ^ m) := by ring
  rw [hval, htopval]
  have hlow' := (abs_le.mp hlow).1
  rw [hexp2] at hlow' ⊢
  have hr₂pos : 0 < r₂ ^ m := by positivity
  have hkey : r₂ ^ m * (5 * c / 8) ≤ r₂ ^ m * ∑' q : T, (g q).re :=
    mul_le_mul_of_nonneg_left htopge hr₂pos.le
  have hkey2 : r₂ ^ m * lowerTail β₀ ℓ m ≤ r₂ ^ m * (c / 8) :=
    mul_le_mul_of_nonneg_left htailm hr₂pos.le
  nlinarith

/-- Level-one constant-vector interval positivity at the scales `y = e^{mℓ}` of one geometric
progression. -/
def JasProgressionPositive (X : ℕ) (ℓ : ℝ) : Prop :=
  ∀ (m : ℕ) (L : ℝ), (X : ℝ) + 1 ≤ Real.exp ((m : ℝ) * ℓ) → 0 ≤ L →
    JasConstProductPositiveOn (jasIntervalPrimes (Real.exp ((m : ℝ) * ℓ)) L) 1

/-- The log-scales off the progression `mℓ`. -/
def offProgression (ℓ : ℝ) : Set ℝ := {u | ∀ m : ℕ, u ≠ (m : ℝ) * ℓ}

theorem jasIntervalProductPositiveExcept_of_jasProgressionPositive {X : ℕ} {ℓ : ℝ}
    (h : JasProgressionPositive X ℓ) : JasIntervalProductPositiveExcept X 1 (offProgression ℓ) := by
  intro y L hy hyS hL
  have hy0 : 0 < y := by linarith [show (0 : ℝ) ≤ X from Nat.cast_nonneg X]
  simp only [offProgression, mem_setOf_eq, not_forall, not_not] at hyS
  obtain ⟨m, hm⟩ := hyS
  have hye : y = Real.exp ((m : ℝ) * ℓ) := by rw [← hm, Real.exp_log hy0]
  rw [hye] at hy ⊢
  exact h m L hy hL

/-- **An attained top and level-one JAS positivity along one geometric progression of scales give
RH.** -/
theorem riemannHypothesis_of_attainedTop_of_jasProgressionPositive
    (hatt : ¬ RiemannHypothesis → ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀) {X : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hpos : JasProgressionPositive X ℓ) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨β₀, hβ₀, htop⟩ := hatt hRH
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = β₀ - 1 / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := htop.2 q
    rw [hαdef]; linarith
  have hαall := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα1 : α < 1 / 2 := by
    obtain ⟨q₀, hq₀⟩ := htop.1
    have := xiZeroCopy_re_lt_one q₀
    rw [hαdef]; linarith
  have hδ0 : 0 < α / 4 := by linarith
  have hc0 : 0 < α / 2 := by linarith
  have hW := eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept
    (jasIntervalProductPositiveExcept_of_jasProgressionPositive hpos) zero_le_one
    hδ0 (by linarith) hc0 (by linarith)
  obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows_except hαall hδ0
    (by linarith) hc0 hW
  have hmax : max (α / 2) (α - min (α / 2) (α / 4 / 4)) = 15 * α / 16 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [hmax] at hM
  obtain ⟨m, -, hm⟩ := exists_lag_progression_gt_exp_of_attainedTop
    (a := 15 * α / 16) (by rw [← hαdef]; linarith) htop hℓ M
  have hL0 : 0 ≤ (m : ℝ) * ℓ := by positivity
  have hnot : (m : ℝ) * ℓ ∉ offProgression ℓ := fun h => h m rfl
  have h1 := hM _ hL0 hnot
  rw [weilLagFunction_eq_ofReal, Complex.ofReal_re] at hm
  linarith [le_abs_self (weilLagFunctionReal ((m : ℝ) * ℓ))]

theorem jasProgressionPositive_of_riemannHypothesis (hRH : RiemannHypothesis) (ℓ : ℝ) :
    ∃ X : ℕ, JasProgressionPositive X ℓ := by
  obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasIntervalProductPositive_one.mp hRH
  exact ⟨X, fun m L hy hL => hX _ L hy hL⟩

/-- **RH ⟺ no off-line chain ∧ level-one JAS positivity at the scales of one geometric
progression.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_jasProgressionPositive {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∃ X : ℕ, JasProgressionPositive X ℓ := by
  constructor
  · intro hRH
    refine ⟨fun hc => ?_, jasProgressionPositive_of_riemannHypothesis hRH ℓ⟩
    obtain ⟨⟨q, hq⟩, -⟩ := hc
    exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
  · rintro ⟨hno, X, hpos⟩
    exact riemannHypothesis_of_attainedTop_of_jasProgressionPositive
      (exists_attainedTop_of_not_jasOffLineChain hno) hℓ hpos

/-- **RH ⟺ zeros approach the line ∧ level-one JAS positivity at the scales of one geometric
progression.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_jasProgressionPositive {ℓ : ℝ} (hℓ : 0 < ℓ) :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ X : ℕ, JasProgressionPositive X ℓ := by
  constructor
  · intro hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH,
      jasProgressionPositive_of_riemannHypothesis hRH ℓ⟩
  · rintro ⟨hZ, X, hpos⟩
    exact riemannHypothesis_of_attainedTop_of_jasProgressionPositive
      (exists_attainedTop_of_zerosApproachLine hZ) hℓ hpos

/-- **Dyadic scales.** RH ⟺ no off-line chain ∧ level-one JAS positivity at the scales `y = 2^m`. -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_jasDyadicScalesPositive :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∃ X : ℕ, JasProgressionPositive X (Real.log 2) :=
  riemannHypothesis_iff_not_jasOffLineChain_and_jasProgressionPositive
    (Real.log_pos one_lt_two)

end

end RHTower
