import GaloisForLFunctions.HTGeometry.PrimeHodgeCubicSylvesterLaw
import GaloisForLFunctions.HTGeometry.PrimeClockGammaTotality
import GaloisForLFunctions.HTGeometry.InjectiveDenseRangePolarUnitary
import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Reachability, faithfulness, properness and the self-financing square

The weighted reachability map `R_d = W_d^*` sends `h ∈ L²((0,∞))` to
`(R_d h)_p = 2√μ_d(p) λ_p^{3/2} ∫₀^∞ r e^{-λ_p r} h(r) dr` (**(PCOB.4)**); `R_d^* e_p = g_p`
(**(PCOB.5)**), `‖R_d‖²_HS = 1` (**(PCOB.6)**) and `R_d R_d^* = A_d` (**(PCOB.7)**).  The joint map
`𝓡_d = Φ^{1/2} ⊗ R_d` has `𝓡_d 𝓡_d^* = 𝖳_d` and `‖𝓡_d‖²_HS = 1` (**(PCOB.9)–(PCOB.10)**).

* **(PCOB.20)–(PCOB.21)** `R_d`, `𝓡_d` are quasiaffinities, so `ker A_d = ker 𝖳_d = 0` and both
  have dense range.
* **(PCOB.22)** The inverse form `q_𝖳(x) = ‖𝖳^{-1/2}x‖²` has compact sublevel sets.
* **(PCOB.23)–(PCOB.26)** `𝓡_d = 𝖳_d^{1/2} V_d` with `V_d` unitary; the unique control of
  `𝖳_d^{1/2} = 𝓡_d B` is `V_d^*`, which is not Hilbert–Schmidt (infinite capital); the unique
  control of `𝖳_d = 𝓡_d B` is `B = 𝓡_d^*` with `‖B‖²_HS = 1` (the square `𝖳_d²` has capital one).
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.ContinuousLinearMap

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

variable {d : ℝ}

/-! ## The frame amplitude -/

/-- The amplitude `√μ_d(p) √((2λ_p)³/2) = 2 √μ_d(p) λ_p^{3/2}`, strictly positive. -/
def primeFrameAmplitude (d : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (primeFormationLaw d p) * Real.sqrt ((2 * Real.log (p : ℝ)) ^ 3 / 2)

theorem primeFrameAmplitude_pos (hd : 0 < d) (p : Nat.Primes) : 0 < primeFrameAmplitude d p :=
  mul_pos (Real.sqrt_pos.2 (primeFormationLaw_pos hd p))
    (Real.sqrt_pos.2 (by have := primeClock_pos p; positivity))

theorem sq_primeFrameAmplitude (hd : 0 < d) (p : Nat.Primes) :
    primeFrameAmplitude d p ^ 2 = 4 * (primeFormationLaw d p * Real.log (p : ℝ) ^ 3) := by
  rw [primeFrameAmplitude, mul_pow, Real.sq_sqrt (primeFormationLaw_pos hd p).le,
    Real.sq_sqrt (by have := primeClock_pos p; positivity)]
  ring

/-! ## The reachability map -/

/-- The weighted reachability map `R_d = W_d^*`. -/
def primeReachability (hd : 0 < d) : HalfLineL2 →L[ℂ] ℓ²P :=
  adjoint (primeCoherentSynthesis 3 hd)

/-- **(PCOB.4)** `(R_d h)_p = 2√μ_d(p) λ_p^{3/2} ∫₀^∞ r e^{-λ_p r} h(r) dr`. -/
theorem primeReachability_apply (hd : 0 < d) (h : HalfLineL2) (p : Nat.Primes) :
    (primeReachability hd h : Nat.Primes → ℂ) p =
      (primeFrameAmplitude d p : ℂ) *
        ∫ r in Ioi (0 : ℝ), ((r * Real.exp (-(Real.log (p : ℝ) * r)) : ℝ) : ℂ) * (h : ℝ → ℂ) r := by
  rw [primeReachability, primeCoherentSynthesis, adjoint_squareSummableSynthesis_apply,
    primeCoherentFrame, inner_smul_left, Complex.conj_ofReal, L2.inner_def, ← integral_const_mul,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [gammaCoherentVector_ae 3 (primeClock_pos p), ae_restrict_mem measurableSet_Ioi]
    with r h1 hr
  have hr' : (0 : ℝ) < r := hr
  rw [h1, RCLike.inner_apply, Complex.conj_ofReal, primeFrameAmplitude, gammaCoherentProfile,
    show ((3 : ℕ) : ℝ) - 1 = 2 by norm_num, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one,
    show (3 - 1 : ℕ).factorial = 2 by rfl]
  push_cast
  ring_nf

/-- **(PCOB.5)** `R_d^* e_p = √μ_d(p) ψ^{(3)}_{λ_p}`. -/
theorem adjoint_primeReachability_single (hd : 0 < d) (p : Nat.Primes) :
    adjoint (primeReachability hd) (lp.single 2 p 1) = primeCoherentFrame 3 d p := by
  rw [primeReachability, adjoint_adjoint, primeCoherentSynthesis_single]

/-- **(PCOB.6)** `‖R_d‖²_HS = 1`. -/
theorem hsNormSq_primeReachability (hd : 0 < d) : hsNormSq (primeReachability hd) = 1 := by
  rw [primeReachability, (show IsHilbertSchmidt (primeCoherentSynthesis 3 hd) from
    squareSummableSynthesis_isHilbertSchmidt _).hsNormSq_adjoint, hsNormSq_primeCoherentSynthesis]

theorem isHilbertSchmidt_primeReachability (hd : 0 < d) : IsHilbertSchmidt (primeReachability hd) :=
  (squareSummableSynthesis_isHilbertSchmidt _).adjoint

/-- **(PCOB.7)** `R_d R_d^* = A_d`. -/
theorem primeReachability_comp_adjoint (hd : 0 < d) :
    primeReachability hd ∘L adjoint (primeReachability hd) = normalizedStokesPrimeOperator hd := by
  refine ext_of_inner_single fun p q => ?_
  rw [primeReachability, adjoint_adjoint, (primeFormationGram_properties (hd := hd)).1 p q,
    normalizedStokesPrimeOperator, lp.inner_single_left, HilbertSchmidt.toOperator_single]
  simp

/-! ## Faithfulness -/

/-- `R_d` is injective: the coherent prime columns are total. -/
theorem primeReachability_injective (hd : 0 < d) : Function.Injective (primeReachability hd) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  refine eq_zero_of_forall_inner_gammaCoherentVector_eq_zero 3 ∅ h fun p _ => ?_
  have hp : (primeReachability hd h : Nat.Primes → ℂ) p = 0 := by
    rw [show primeReachability hd h = 0 from hh]
    rfl
  rw [primeReachability, primeCoherentSynthesis, adjoint_squareSummableSynthesis_apply,
    primeCoherentFrame, inner_smul_left, Complex.conj_ofReal] at hp
  exact (mul_eq_zero.1 hp).resolve_left
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (primeFormationLaw_pos hd p)).ne')

/-- **(PCOB.20)** `R_d` has dense range. -/
theorem denseRange_primeReachability (hd : 0 < d) : DenseRange (primeReachability hd) :=
  denseRange_adjoint_of_injective (primeCoherentSynthesis_injective 3 hd)

/-- **(PCOB.21)** `ker A_d = 0`. -/
theorem normalizedStokesPrimeOperator_injective (hd : 0 < d) :
    Function.Injective (normalizedStokesPrimeOperator hd) := by
  rw [← primeReachability_comp_adjoint hd]
  intro x y hxy
  have h1 : ∀ z, ‖adjoint (primeReachability hd) z‖ ^ 2 =
      (⟪z, (primeReachability hd ∘L adjoint (primeReachability hd)) z⟫_ℂ).re := fun z => by
    rw [comp_apply, ← adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hz : (primeReachability hd ∘L adjoint (primeReachability hd)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h2 := h1 (x - y)
  rw [hz, inner_zero_right, Complex.zero_re] at h2
  have h3 : adjoint (primeReachability hd) (x - y) = 0 :=
    norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  rw [primeReachability, adjoint_adjoint] at h3
  exact sub_eq_zero.1 (primeCoherentSynthesis_injective 3 hd (h3.trans (map_zero _).symm))

/-- **(PCOB.21)** `A_d` has dense range. -/
theorem denseRange_normalizedStokesPrimeOperator (hd : 0 < d) :
    DenseRange (normalizedStokesPrimeOperator hd) := by
  have hsa : adjoint (normalizedStokesPrimeOperator hd) = normalizedStokesPrimeOperator hd := by
    rw [← primeReachability_comp_adjoint hd, adjoint_comp, adjoint_adjoint]
  have := denseRange_adjoint_of_injective (normalizedStokesPrimeOperator_injective hd)
  rwa [hsa] at this

/-! ## The joint reachability map -/

local notation "ℓ²H" => lp (fun _ : ℕ => HalfLineL2) 2

/-- The joint reachability map `𝓡_d = Φ^{1/2} ⊗ R_d = Q_d^*`. -/
def jointReachability (hd : 0 < d) : ℓ²H →L[ℂ] PrimeHodgeHistoryHilbert :=
  adjoint (historyFormationChannel hd)

/-- **(PCOB.9)** `𝖳_d = 𝓡_d 𝓡_d^*`. -/
theorem jointReachability_comp_adjoint (hd : 0 < d) :
    jointReachability hd ∘L adjoint (jointReachability hd) = primeHodgeHistoryDefectOperator hd := by
  rw [jointReachability, adjoint_adjoint, adjoint_comp_historyFormationChannel]

theorem isHilbertSchmidt_jointReachability (hd : 0 < d) :
    IsHilbertSchmidt (jointReachability hd) :=
  (squareSummableSynthesis_isHilbertSchmidt _).adjoint

/-- **(PCOB.10)** `‖𝓡_d‖²_HS = Tr 𝖳_d = 1`. -/
theorem hsNormSq_jointReachability (hd : 0 < d) : hsNormSq (jointReachability hd) = 1 := by
  rw [jointReachability, (show IsHilbertSchmidt (historyFormationChannel hd) from
    squareSummableSynthesis_isHilbertSchmidt _).hsNormSq_adjoint, hsNormSq_historyFormationChannel]

/-- The `n`-th history row of a history–prime vector. -/
def historyRow (x : PrimeHodgeHistoryHilbert) (n : ℕ) : ℓ²P :=
  ⟨fun p => x (n, p), HilbertSchmidt.memℓp_of_sq
    ((HilbertSchmidt.summable_coe_sq x).comp_injective (fun p q h => by
      simpa using congrArg Prod.snd h))⟩

theorem inner_historyPrimeFrame_single (np : ℕ × Nat.Primes) (n : ℕ)
    (f : HalfLineL2) :
    ⟪historyPrimeFrame d np, (lp.single 2 n f : ℓ²H)⟫_ℂ =
      if np.1 = n then ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) *
        ⟪primeCoherentFrame 3 d np.2, f⟫_ℂ else 0 := by
  obtain ⟨m, p⟩ := np
  rw [historyPrimeFrame, inner_smul_left, Complex.conj_ofReal, lp.inner_single_right]
  simp only
  by_cases hmn : m = n
  · subst hmn
    rw [lp.single_apply_self, if_pos rfl, primeCoherentFrame, inner_smul_left, Complex.conj_ofReal,
      Real.sqrt_mul (PrimeHodgeHistory.w_pos m).le]
    push_cast
    ring
  · rw [lp.single_apply_ne _ _ _ (Ne.symm hmn), inner_zero_left, mul_zero, if_neg hmn]

/-- `⟪Q_d x, e_n ⊗ f⟫ = √w_n ⟪W_d x_n, f⟫`. -/
theorem inner_historyFormationChannel_single (hd : 0 < d) (x : PrimeHodgeHistoryHilbert) (n : ℕ)
    (f : HalfLineL2) :
    ⟪historyFormationChannel hd x, (lp.single 2 n f : ℓ²H)⟫_ℂ =
      ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) *
        ⟪primeCoherentSynthesis 3 hd (historyRow x n), f⟫_ℂ := by
  rw [← adjoint_inner_right, ← adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum]
  set g : ℕ × Nat.Primes → ℂ := fun mp => ⟪(x : ℕ × Nat.Primes → ℂ) mp,
    (adjoint (historyFormationChannel hd) (lp.single 2 n f) : ℕ × Nat.Primes → ℂ) mp⟫_ℂ
  have hg : Summable g := lp.summable_inner _ _
  have hrow : ∀ m p, g (m, p) = if m = n then ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) *
      ⟪(historyRow x n : Nat.Primes → ℂ) p,
        (adjoint (primeCoherentSynthesis 3 hd) f : Nat.Primes → ℂ) p⟫_ℂ else 0 := fun m p => by
    simp only [g]
    rw [historyFormationChannel, adjoint_squareSummableSynthesis_apply,
      inner_historyPrimeFrame_single, primeCoherentSynthesis,
      adjoint_squareSummableSynthesis_apply]
    simp only
    split_ifs with hmn
    · subst hmn
      simp only [historyRow, RCLike.inner_apply]
      ring
    · simp
  rw [hg.tsum_prod, tsum_eq_single n (fun m hm => by simp_rw [hrow, if_neg hm, tsum_zero]),
    tsum_congr fun p => (hrow n p).trans (if_pos rfl), tsum_mul_left]

/-- `Q_d` is injective. -/
theorem historyFormationChannel_injective (hd : 0 < d) :
    Function.Injective (historyFormationChannel hd) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hrow : ∀ n, historyRow x n = 0 := fun n => by
    refine primeCoherentSynthesis_injective 3 hd ?_
    rw [map_zero]
    refine ext_inner_right ℂ fun f => ?_
    have h := inner_historyFormationChannel_single hd x n f
    rw [hx, inner_zero_left] at h
    rw [inner_zero_left]
    exact (mul_eq_zero.1 h.symm).resolve_left
      (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (PrimeHodgeHistory.w_pos n)).ne')
  refine lp.ext (funext fun np => ?_)
  have h1 : (historyRow x np.1 : Nat.Primes → ℂ) np.2 = 0 := by
    rw [hrow]
    rfl
  exact h1

/-- `Q_d^*` is injective: the history–prime frame is total. -/
theorem adjoint_historyFormationChannel_injective (hd : 0 < d) :
    Function.Injective (adjoint (historyFormationChannel hd)) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  refine lp.ext (funext fun n => ?_)
  refine eq_zero_of_forall_inner_gammaCoherentVector_eq_zero 3 ∅ _ fun p _ => ?_
  have h := congrArg (fun z : PrimeHodgeHistoryHilbert => (z : ℕ × Nat.Primes → ℂ) (n, p)) hy
  simp only [historyFormationChannel, adjoint_squareSummableSynthesis_apply] at h
  rw [historyPrimeFrame, inner_smul_left, Complex.conj_ofReal, lp.inner_single_left] at h
  simp only [lp.coeFn_zero, Pi.zero_apply] at h ⊢
  exact (mul_eq_zero.1 h).resolve_left (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2
    (mul_pos (PrimeHodgeHistory.w_pos n) (primeFormationLaw_pos hd p))).ne')

/-- **(PCOB.20)** `𝓡_d` is a quasiaffinity. -/
theorem jointReachability_injective (hd : 0 < d) : Function.Injective (jointReachability hd) :=
  adjoint_historyFormationChannel_injective hd

theorem denseRange_jointReachability (hd : 0 < d) : DenseRange (jointReachability hd) :=
  denseRange_adjoint_of_injective (historyFormationChannel_injective hd)

/-- **(PCOB.21)** `ker 𝖳_d = 0` and `𝖳_d` has dense range. -/
theorem primeHodgeHistoryDefectOperator_injective (hd : 0 < d) :
    Function.Injective (primeHodgeHistoryDefectOperator hd) := by
  rw [← adjoint_comp_historyFormationChannel]
  intro x y hxy
  have hz : (adjoint (historyFormationChannel hd) ∘L historyFormationChannel hd) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h2 : ‖historyFormationChannel hd (x - y)‖ ^ 2 = 0 := by
    have e : ‖historyFormationChannel hd (x - y)‖ ^ 2 =
        (⟪x - y, (adjoint (historyFormationChannel hd) ∘L historyFormationChannel hd) (x - y)⟫_ℂ).re := by
      rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [e, hz, inner_zero_right, Complex.zero_re]
  have h3 : historyFormationChannel hd (x - y) = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  exact sub_eq_zero.1 (historyFormationChannel_injective hd (h3.trans (map_zero _).symm))

theorem denseRange_primeHodgeHistoryDefectOperator (hd : 0 < d) :
    DenseRange (primeHodgeHistoryDefectOperator hd) := by
  have hsa : adjoint (primeHodgeHistoryDefectOperator hd) = primeHodgeHistoryDefectOperator hd := by
    rw [← adjoint_comp_historyFormationChannel, adjoint_comp, adjoint_adjoint]
  have := denseRange_adjoint_of_injective (primeHodgeHistoryDefectOperator_injective hd)
  rwa [hsa] at this

/-! ## Polar decomposition and properness -/

/-- `𝖳_d^{1/2} = (𝓡_d 𝓡_d^*)^{1/2}`. -/
def jointRoot (hd : 0 < d) : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  leftModulus (jointReachability hd)

/-- The unitary polar factor `V_d`. -/
def jointPolarUnitary (hd : 0 < d) : ℓ²H ≃ₗᵢ[ℂ] PrimeHodgeHistoryHilbert :=
  polarUnitary (jointReachability hd) (jointReachability_injective hd) (denseRange_jointReachability hd)

theorem jointRoot_comp_self (hd : 0 < d) :
    jointRoot hd ∘L jointRoot hd = primeHodgeHistoryDefectOperator hd := by
  rw [jointRoot, leftModulus_comp_self, jointReachability_comp_adjoint]

/-- **(PCOB.23)** `𝓡_d = 𝖳_d^{1/2} V_d`. -/
theorem jointRoot_comp_polarUnitary (hd : 0 < d) :
    jointRoot hd ∘L (jointPolarUnitary hd : ℓ²H →L[ℂ] PrimeHodgeHistoryHilbert) = jointReachability hd :=
  leftModulus_comp_polarUnitary _ _ _

theorem jointRoot_eq (hd : 0 < d) :
    jointRoot hd = jointReachability hd ∘L
      ((jointPolarUnitary hd).symm : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H) := by
  refine ContinuousLinearMap.ext fun x => ?_
  exact (apply_polarUnitary_symm (jointReachability hd) (jointReachability_injective hd)
    (denseRange_jointReachability hd) x).symm

theorem isCompactOperator_jointRoot (hd : 0 < d) : IsCompactOperator (jointRoot hd) := by
  rw [jointRoot_eq]
  exact (isHilbertSchmidt_jointReachability hd).isCompactOperator.comp_clm _

theorem jointRoot_injective (hd : 0 < d) : Function.Injective (jointRoot hd) :=
  injective_leftModulus (denseRange_jointReachability hd)

theorem separableSpace_lp_countable {ι : Type*} [Countable ι] [DecidableEq ι] :
    TopologicalSpace.SeparableSpace (lp (fun _ : ι => ℂ) 2) := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ι)) : Set (lp (fun _ : ι => ℂ) 2)) :=
    (Set.countable_range _).isSeparable.span
  have hd := (HilbertSchmidt.lpBasis ι).dense_span
  have := hs.closure
  rwa [← Submodule.topologicalClosure_coe, hd, Submodule.top_coe] at this

instance : TopologicalSpace.SeparableSpace PrimeHodgeHistoryHilbert := separableSpace_lp_countable

/-- The sublevel set `{x : q_𝖳(x) ≤ C}` of the inverse form `q_𝖳(x) = ‖𝖳^{-1/2}x‖²`. -/
def inverseFormSublevel (hd : 0 < d) (C : ℝ) : Set PrimeHodgeHistoryHilbert :=
  {x | ∃ y, ‖y‖ ^ 2 ≤ C ∧ jointRoot hd y = x}

/-- The inverse form is well defined: `𝖳^{1/2}` is injective. -/
theorem inverseForm_preimage_unique (hd : 0 < d) {y y' : PrimeHodgeHistoryHilbert}
    (h : jointRoot hd y = jointRoot hd y') : y = y' :=
  jointRoot_injective hd h

/-- **(PCOB.22) Properness.**  Every sublevel set of the inverse form is compact. -/
theorem isCompact_inverseFormSublevel (hd : 0 < d) (C : ℝ) : IsCompact (inverseFormSublevel hd C) := by
  rcases lt_or_ge C 0 with hC | hC
  · convert isCompact_empty
    refine Set.eq_empty_of_forall_notMem fun x ⟨y, hy, _⟩ => ?_
    linarith [sq_nonneg ‖y‖]
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  choose y hy hyx using hx
  have hbound : ∀ n, ‖y n‖ ≤ Real.sqrt C := fun n =>
    Real.le_sqrt_of_sq_le (hy n)
  obtain ⟨w, φ, hφ, hw, hweak⟩ := exists_weaklyConvergent_subseq_of_bounded y _ hbound
  refine ⟨jointRoot hd w, ⟨w, ?_, rfl⟩, φ, hφ, ?_⟩
  · calc ‖w‖ ^ 2 ≤ Real.sqrt C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ = C := Real.sq_sqrt hC
  set c : ℝ := 2 * Real.sqrt C + 1
  have hc : 0 < c := by positivity
  set u : ℕ → PrimeHodgeHistoryHilbert := fun n => (c⁻¹ : ℂ) • (y (φ n) - w)
  have hu1 : ∀ n, ‖u n‖ ≤ 1 := fun n => by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
    rw [inv_mul_le_iff₀ hc, mul_one]
    calc ‖y (φ n) - w‖ ≤ ‖y (φ n)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ Real.sqrt C + Real.sqrt C := add_le_add (hbound _) hw
      _ ≤ c := by simp only [c]; linarith
  have huweak : ∀ z, Tendsto (fun n => ⟪z, u n⟫_ℂ) atTop (𝓝 0) := fun z => by
    have h1 : Tendsto (fun n => ⟪y (φ n) - w, z⟫_ℂ) atTop (𝓝 0) := by
      have := (hweak z).sub (tendsto_const_nhds (x := ⟪w, z⟫_ℂ))
      rw [sub_self] at this
      exact this.congr fun n => by rw [inner_sub_left]
    have h2 := ((Complex.continuous_conj.tendsto 0).comp h1).const_mul (c⁻¹ : ℂ)
    rw [map_zero, mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [u, Function.comp_apply, inner_smul_right]
    rw [inner_conj_symm]
  have hK := tendsto_norm_compact_of_weaklyNull (jointRoot hd) (isCompactOperator_jointRoot hd) u hu1
    huweak
  have hK' := hK.const_smul (c : ℂ)
  rw [smul_zero] at hK'
  have hlim : Tendsto (fun n => jointRoot hd (y (φ n)) - jointRoot hd w) atTop (𝓝 0) :=
    hK'.congr fun n => by
      simp only [u, map_smul, smul_smul, map_sub]
      rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hc.ne'), one_smul]
  have := hlim.add_const (jointRoot hd w)
  rw [zero_add] at this
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, sub_add_cancel, hyx]

/-! ## Formation capital -/

/-- **(PCOB.24)** `𝓡_d V_d^* = 𝖳_d^{1/2}`. -/
theorem jointReachability_comp_polarUnitary_symm (hd : 0 < d) :
    jointReachability hd ∘L ((jointPolarUnitary hd).symm : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H) =
      jointRoot hd :=
  (jointRoot_eq hd).symm

/-- The control of the critical amplitude `𝖳_d^{1/2} = 𝓡_d B` is unique: `B = V_d^*`. -/
theorem eq_polarUnitary_symm_of_comp (hd : 0 < d) {B : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H}
    (hB : jointReachability hd ∘L B = jointRoot hd) :
    B = ((jointPolarUnitary hd).symm : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H) := by
  refine ContinuousLinearMap.ext fun x => jointReachability_injective hd ?_
  have h1 := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert => A x) hB
  have h2 := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert => A x)
    (jointReachability_comp_polarUnitary_symm hd)
  simp only [comp_apply] at h1 h2
  rw [h1, h2]

theorem not_finiteDimensional_primeHodgeHistoryHilbert :
    ¬ FiniteDimensional ℂ PrimeHodgeHistoryHilbert := by
  intro hfin
  have hli : LinearIndependent ℂ (HilbertSchmidt.lpBasis (ℕ × Nat.Primes)) :=
    (HilbertSchmidt.lpBasis (ℕ × Nat.Primes)).orthonormal.linearIndependent
  have := hli.finite
  exact not_finite (ℕ × Nat.Primes)

/-- **(PCOB.24) Infinite capital.**  The unique control `V_d^*` of `𝖳_d^{1/2}` is not
Hilbert–Schmidt. -/
theorem not_isHilbertSchmidt_polarUnitary_symm (hd : 0 < d) :
    ¬ IsHilbertSchmidt ((jointPolarUnitary hd).symm : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H) := by
  intro hHS
  apply not_finiteDimensional_primeHodgeHistoryHilbert
  refine FiniteDimensional.of_isCompactOperator_id ?_
  have hc := hHS.isCompactOperator.clm_comp
    ((jointPolarUnitary hd) : ℓ²H →L[ℂ] PrimeHodgeHistoryHilbert)
  have hid : (id : PrimeHodgeHistoryHilbert → PrimeHodgeHistoryHilbert) =
      ⇑((jointPolarUnitary hd) : ℓ²H →L[ℂ] PrimeHodgeHistoryHilbert) ∘
        ⇑((jointPolarUnitary hd).symm : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H) := by
    funext x
    simp
  rw [hid]
  exact hc

/-- **(PCOB.25)–(PCOB.26) The self-financing square.**  `𝖳_d = 𝓡_d 𝓡_d^*`, `𝖳_d² = 𝖳_d 𝖳_d^*`,
the control `B = 𝓡_d^*` has `‖B‖²_HS = Tr 𝖳_d = 1`, and it is the unique bounded control. -/
theorem selfFinancingSquare (hd : 0 < d) :
    primeHodgeHistoryDefectOperator hd = jointReachability hd ∘L adjoint (jointReachability hd) ∧
      primeHodgeHistoryDefectOperator hd ∘L primeHodgeHistoryDefectOperator hd =
        primeHodgeHistoryDefectOperator hd ∘L adjoint (primeHodgeHistoryDefectOperator hd) ∧
      hsNormSq (adjoint (jointReachability hd)) = 1 ∧
      ∀ B : PrimeHodgeHistoryHilbert →L[ℂ] ℓ²H,
        jointReachability hd ∘L B = primeHodgeHistoryDefectOperator hd →
          B = adjoint (jointReachability hd) := by
  have hsa : adjoint (primeHodgeHistoryDefectOperator hd) = primeHodgeHistoryDefectOperator hd := by
    rw [← adjoint_comp_historyFormationChannel, adjoint_comp, adjoint_adjoint]
  refine ⟨(jointReachability_comp_adjoint hd).symm, by rw [hsa], ?_, fun B hB => ?_⟩
  · rw [(isHilbertSchmidt_jointReachability hd).hsNormSq_adjoint, hsNormSq_jointReachability]
  · refine ContinuousLinearMap.ext fun x => jointReachability_injective hd ?_
    have h1 := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert => A x) hB
    have h2 := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert => A x)
      (jointReachability_comp_adjoint hd)
    simp only [comp_apply] at h1 h2
    rw [h1, h2]

end GaloisForLFunctions.HTGeometry
