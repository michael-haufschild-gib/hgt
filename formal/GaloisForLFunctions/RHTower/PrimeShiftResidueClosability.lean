import GaloisForLFunctions.RHTower.PrimeCharacterTailIndependence
import GaloisForLFunctions.RHTower.PrimeShiftCharacterBasic
import GaloisForLFunctions.RHTower.PrimeShiftCriticalSummability
import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The prime-shift residue graph and its closability

The normalized prime shift characters of the open right half of the critical strip lie in the
critical summable layer, hence in the vanishing-tail layer `M_0` of the logarithmic Marcinkiewicz
geometry.  They are linearly independent modulo finite prime support, so the residue of the
continued grade-one prime source defines a canonical linear functional on the algebraic sum of the
finitely supported fields and the character span.  That functional vanishes on every finite Euler
field, and it is closable exactly when the Riemann hypothesis holds.
-/

namespace RHTower

open Filter Complex
open scoped Topology BigOperators

/-! ## Characters and the critical summable layer -/

/-- **The exact shift law.**  The prime-log Dirichlet series weighted by a shift character is the
grade-one prime source translated by that shift. -/
theorem tsum_primeLog_mul_primeShiftCharacter (z s : ℂ) (hs : 1 < (s + z - 1 / 2).re) :
    ∑' p : Nat.Primes,
        (Real.log ((p : ℕ) : ℝ) : ℂ) * primeShiftCharacter z (p : ℕ) / ((p : ℂ) ^ s)
      = xiPrimeLogDirichlet (s + z - 1 / 2) := by
  rw [xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs]
  refine tsum_congr fun p => ?_
  have hne : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.pos.ne'
  have hL : (((p : ℕ) : ℂ)) ^ ((1 : ℂ) / 2 - z) / (((p : ℕ) : ℂ) ^ s)
      = (((p : ℕ) : ℂ)) ^ (-(s + z - 1 / 2)) := by
    rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
    congr 1
    ring
  rw [primeShiftCharacter, if_pos p.2, mul_div_assoc, hL, Complex.cpow_neg, ← div_eq_mul_inv]

/-! ## The Marcinkiewicz null topology -/

/-- The logarithmic Marcinkiewicz seminorm of a complex field is at most `ε`. -/
def MarcinkiewiczSmall (b : ℕ → ℂ) (ε : ℝ) : Prop :=
  ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient (absField b) X ≤ ε

/-- A sequence of fields tends to zero in the logarithmic Marcinkiewicz seminorm. -/
def TendstoMarcinkiewiczZero (x : ℕ → (ℕ → ℂ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MarcinkiewiczSmall (x n) ε

/-- The tail of a complex coefficient field beyond a truncation point. -/
def primeFieldTail (b : ℕ → ℂ) (P : ℕ) : ℕ → ℂ := fun n => if P < n then b n else 0

/-- The head of a complex coefficient field up to a truncation point. -/
def primeFieldHead (b : ℕ → ℂ) (P : ℕ) : ℕ → ℂ := fun n => if P < n then 0 else b n

theorem absField_primeFieldTail (b : ℕ → ℂ) (P : ℕ) :
    absField (primeFieldTail b P) = primeCoefficientTail (absField b) P := by
  funext n
  by_cases h : P < n <;> simp [absField, primeFieldTail, primeCoefficientTail, h]

theorem sub_primeFieldHead (b : ℕ → ℂ) (P : ℕ) : b - primeFieldHead b P = primeFieldTail b P := by
  funext n
  by_cases h : P < n <;> simp [primeFieldHead, primeFieldTail, h]

theorem finite_support_primeFieldHead (b : ℕ → ℂ) (P : ℕ) :
    (Function.support (primeFieldHead b P)).Finite := by
  refine Set.Finite.subset (Set.finite_Iic P) fun n hn => ?_
  have hn' : primeFieldHead b P n ≠ 0 := hn
  by_cases h : P < n
  · exact absurd (by simp [primeFieldHead, h]) hn'
  · simpa using Nat.not_lt.mp h

/-- Vanishing tails give a Marcinkiewicz null sequence of truncation tails. -/
theorem tendstoMarcinkiewiczZero_tail {b : ℕ → ℂ}
    (hb : MemVanishingTailLayer (absField b)) :
    TendstoMarcinkiewiczZero (fun n => primeFieldTail b n) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hb ε hε
  refine ⟨P, fun n hn X hX => ?_⟩
  rw [absField_primeFieldTail]
  have hlogX : (0 : ℝ) < Real.log X := log_cutoff_pos hX
  have hanti := primeLogMass_tail_anti (absField b) hn X
  have hPX := hP X hX
  unfold marcinkiewiczLogQuotient at hPX ⊢
  rw [div_le_iff₀ hlogX] at hPX ⊢
  linarith

/-! ## The canonical shift residue -/

theorem analyticAt_riemannZeta_primeShiftResidueClosability {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ riemannZeta z := by
  have hdon : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    fun w hw => (differentiableAt_riemannZeta (by simpa using hw)).differentiableWithinAt
  exact hdon.analyticOnNhd isOpen_compl_singleton z (by simpa using hz)

theorem analyticOrderAt_riemannZeta_ne_top {z : ℂ} (hz : z ≠ 1) :
    analyticOrderAt riemannZeta z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hev := htop
  have hdon : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    fun w hw => (differentiableAt_riemannZeta (by simpa using hw)).differentiableWithinAt
  have hana_on : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    hdon.analyticOnNhd isOpen_compl_singleton
  have hpreconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have heqon : Set.EqOn riemannZeta 0 {(1 : ℂ)}ᶜ :=
    hana_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpreconn (by simpa using hz) hev
  have hζ2ne : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  exact hζ2ne (by simpa using heqon (show (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) by norm_num))

/-- The multiplicity of the zeta divisor at a point. -/
noncomputable def zetaMultiplicity (z : ℂ) : ℕ := analyticOrderNatAt riemannZeta z

/-- The canonical shift residue of the continued grade-one prime source at a point:  minus the
order of the zeta divisor there. -/
noncomputable def primeShiftResidue (z : ℂ) : ℂ := -(zetaMultiplicity z : ℂ)

theorem zetaMultiplicity_eq_zero_iff {z : ℂ} (hz : z ≠ 1) :
    zetaMultiplicity z = 0 ↔ riemannZeta z ≠ 0 := by
  have hana := analyticAt_riemannZeta_primeShiftResidueClosability hz
  have hne := analyticOrderAt_riemannZeta_ne_top hz
  rw [zetaMultiplicity, analyticOrderNatAt, ENat.toNat_eq_zero]
  constructor
  · rintro (h0 | htop)
    · exact hana.analyticOrderAt_eq_zero.mp h0
    · exact absurd htop hne
  · intro hz0
    exact Or.inl (hana.analyticOrderAt_eq_zero.mpr hz0)

theorem primeShiftResidue_eq_zero_iff {z : ℂ} (hz : z ≠ 1) :
    primeShiftResidue z = 0 ↔ riemannZeta z ≠ 0 := by
  rw [primeShiftResidue, neg_eq_zero, ← zetaMultiplicity_eq_zero_iff hz]
  exact_mod_cast Iff.rfl

/-- **The canonical residue law.**  On the right half of the critical strip the continued
grade-one prime source has residue exactly minus the zeta multiplicity at every point. -/
theorem tendsto_sub_mul_xiPrimeLogDirichletContinuation {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) :
    Tendsto (fun s : ℂ => (s - z) * xiPrimeLogDirichletContinuation s)
      (𝓝[≠] z) (𝓝 (primeShiftResidue z)) := by
  have hlin := RHTower.tendsto_sub_self_punctured_zero z
  have htail : Tendsto (fun s : ℂ => xiPrimeLogHigherValuation s)
      (𝓝[≠] z) (𝓝 (xiPrimeLogHigherValuation z)) :=
    (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hz).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have htail0 := hlin.mul htail
  by_cases hzero : riemannZeta z = 0
  · have hana := analyticAt_riemannZeta_primeShiftResidueClosability hz1
    have hnetop := analyticOrderAt_riemannZeta_ne_top hz1
    obtain ⟨g, hg, hg0, hfac⟩ := hana.analyticOrderAt_ne_top.mp hnetop
    have hres := logDeriv_residue_of_factorization (n := zetaMultiplicity z) hg hg0 hfac
    have hflux : Tendsto (fun s : ℂ => (s - z) * infinitePrimeFlux s)
        (𝓝[≠] z) (𝓝 (primeShiftResidue z)) := by
      have := hres.neg
      simp only [primeShiftResidue]
      refine this.congr' (Filter.Eventually.of_forall fun s => ?_)
      simp only [infinitePrimeFlux, logDeriv_apply]
      ring
    have hsub := hflux.sub htail0
    simpa only [xiPrimeLogDirichletContinuation, mul_sub, zero_mul, sub_zero] using hsub
  · have hres0 : primeShiftResidue z = 0 := (primeShiftResidue_eq_zero_iff hz1).mpr hzero
    rw [hres0]
    have hdiff : DifferentiableAt ℂ xiPrimeLogDirichletContinuation z := by
      have hflux : DifferentiableAt ℂ infinitePrimeFlux z := by
        simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using!
          differentiableAt_neg_logDeriv_riemannZeta hz1 hzero
      exact hflux.sub (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hz)
    have hcont : Tendsto (fun s : ℂ => xiPrimeLogDirichletContinuation s)
        (𝓝[≠] z) (𝓝 (xiPrimeLogDirichletContinuation z)) :=
      hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hlin.mul hcont


/-! ## Closure properties of the critical summable layer -/

theorem memCriticalSummableLayer_absField_add {b c : ℕ → ℂ}
    (hb : MemCriticalSummableLayer (absField b)) (hc : MemCriticalSummableLayer (absField c)) :
    MemCriticalSummableLayer (absField (b + c)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hb.add hc)
  · refine Set.indicator_nonneg (fun m _ => ?_) n
    have : (0 : ℝ) ≤ Real.log m / (m : ℝ) :=
      div_nonneg (Real.log_natCast_nonneg m) (Nat.cast_nonneg m)
    positivity
  · by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      have hw : (0 : ℝ) ≤ Real.log n / (n : ℝ) :=
        div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
      have htri : |absField (b + c) n| ≤ |absField b n| + |absField c n| := by
        rw [abs_of_nonneg (absField_nonneg _ n), abs_of_nonneg (absField_nonneg _ n),
          abs_of_nonneg (absField_nonneg _ n)]
        simpa [absField] using norm_add_le (b n) (c n)
      calc Real.log n / (n : ℝ) * |absField (b + c) n|
          ≤ Real.log n / (n : ℝ) * (|absField b n| + |absField c n|) :=
            mul_le_mul_of_nonneg_left htri hw
        _ = Real.log n / (n : ℝ) * |absField b n| + Real.log n / (n : ℝ) * |absField c n| := by
            ring
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
      simp

theorem memCriticalSummableLayer_absField_smul (a : ℂ) {b : ℕ → ℂ}
    (hb : MemCriticalSummableLayer (absField b)) :
    MemCriticalSummableLayer (absField (a • b)) := by
  have hEq : {p : ℕ | p.Prime}.indicator
      (fun n => Real.log n / (n : ℝ) * |absField (a • b) n|)
      = fun n => ‖a‖ * ({p : ℕ | p.Prime}.indicator
        (fun n => Real.log n / (n : ℝ) * |absField b n|) n) := by
    funext n
    by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      rw [abs_of_nonneg (absField_nonneg _ n), abs_of_nonneg (absField_nonneg _ n)]
      simp only [absField, Pi.smul_apply, norm_smul]
      ring
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
      simp
  rw [MemCriticalSummableLayer, hEq]
  exact hb.mul_left _

theorem memCriticalSummableLayer_absField_zero :
    MemCriticalSummableLayer (absField (0 : ℕ → ℂ)) := by
  refine memCriticalSummableLayer_of_finite_support ∅ fun n _ => ?_
  simp [absField]

theorem memCriticalSummableLayer_absField_finsetSum {ι : Type*} (S : Finset ι)
    (F : ι → ℕ → ℂ) (hF : ∀ i ∈ S, MemCriticalSummableLayer (absField (F i))) :
    MemCriticalSummableLayer (absField (∑ i ∈ S, F i)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      exact memCriticalSummableLayer_absField_zero
  | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact memCriticalSummableLayer_absField_add (hF i (Finset.mem_insert_self i S))
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-! ## The canonical residue functional -/

/-- The open right half of the critical strip. -/
def RightStrip : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 1}

/-- A point of the open right half of the critical strip. -/
private abbrev StripPoint := {z : ℂ // z ∈ RightStrip}

theorem stripPoint_ne_one (z : StripPoint) : (z : ℂ) ≠ 1 := by
  intro h
  have h2 := z.2.2
  rw [h] at h2
  simp at h2

theorem stripPoint_half_lt_re (z : StripPoint) : 1 / 2 < (z : ℂ).re := z.2.1

/-- The character field attached to a finitely supported coefficient system on the strip. -/
noncomputable def stripCharacterField : (StripPoint →₀ ℂ) →ₗ[ℂ] (ℕ → ℂ) :=
  Finsupp.linearCombination ℂ fun z : StripPoint => primeShiftCharacter (z : ℂ)

/-- The residue value of a finitely supported coefficient system on the strip. -/
noncomputable def stripResidueValue : (StripPoint →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun z : StripPoint => primeShiftResidue (z : ℂ)

theorem stripCharacterField_eq_sum (u : StripPoint →₀ ℂ) :
    stripCharacterField u = ∑ z ∈ u.support, u z • primeShiftCharacter (z : ℂ) := by
  rw [stripCharacterField, Finsupp.linearCombination_apply, Finsupp.sum]

theorem stripCharacterField_apply (u : StripPoint →₀ ℂ) (n : ℕ) :
    stripCharacterField u n = ∑ z ∈ u.support, u z * primeShiftCharacter (z : ℂ) n := by
  rw [stripCharacterField_eq_sum]
  simp [Finset.sum_apply]

theorem stripResidueValue_apply (u : StripPoint →₀ ℂ) :
    stripResidueValue u = ∑ z ∈ u.support, u z * primeShiftResidue (z : ℂ) := by
  rw [stripResidueValue, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

/-- The domain map of the canonical residue functional. -/
noncomputable def residueDomainMap :
    ((ℕ →₀ ℂ) × (StripPoint →₀ ℂ)) →ₗ[ℂ] (ℕ → ℂ) :=
  Finsupp.lcoeFun.comp (LinearMap.fst ℂ (ℕ →₀ ℂ) (StripPoint →₀ ℂ)) +
    stripCharacterField.comp (LinearMap.snd ℂ (ℕ →₀ ℂ) (StripPoint →₀ ℂ))

theorem residueDomainMap_apply (fu : (ℕ →₀ ℂ) × (StripPoint →₀ ℂ)) :
    residueDomainMap fu = (fun n => fu.1 n) + stripCharacterField fu.2 := rfl

theorem injective_residueDomainMap : Function.Injective residueDomainMap := by
  classical
  haveI : DecidableEq StripPoint := Classical.decEq _
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨f, u⟩ hfu
  rw [LinearMap.mem_ker, residueDomainMap_apply] at hfu
  have hpt : ∀ n : ℕ, f n + ∑ z ∈ u.support, u z * primeShiftCharacter (z : ℂ) n = 0 := by
    intro n
    have hval := congrFun hfu n
    rw [← stripCharacterField_apply]
    simpa using hval
  have huzero : ∀ z ∈ u.support, u z = 0 := by
    refine primeCharacter_coeff_eq_zero_of_eventually_vanishing
      (c := fun z : StripPoint => u z) (x := fun z : StripPoint => (z : ℂ) - 1 / 2)
      u.support ?_ ?_
    · intro i _ j _ hij
      apply Subtype.ext
      have hval : (i : ℂ) = (j : ℂ) := by linear_combination hij
      exact hval
    · refine ⟨f.support.sup id + 1, fun p hp hPp => ?_⟩
      have hpf : f p = 0 := by
        by_contra hne
        have hmem : p ∈ f.support := Finsupp.mem_support_iff.mpr hne
        have hle : p ≤ f.support.sup id := Finset.le_sup (f := id) hmem
        omega
      have hrel := hpt p
      rw [hpf, zero_add] at hrel
      refine hrel.symm.trans ?_ |>.symm
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      rw [primeShiftCharacter, if_pos hp]
      congr 1
      ring
  have hu0 : u = 0 := by
    ext z
    by_cases hz : z ∈ u.support
    · simpa using huzero z hz
    · simpa using Finsupp.notMem_support_iff.mp hz
  have hf0 : f = 0 := by
    ext n
    have hval := hpt n
    rw [hu0] at hval
    simpa using hval
  simp [hf0, hu0]

/-- The domain of the canonical residue functional. -/
noncomputable def residueDomain : Submodule ℂ (ℕ → ℂ) :=
  LinearMap.range residueDomainMap

/-- **The canonical residue functional.**  It reads the residue of the continued grade-one prime
source off a finite character combination and ignores every finite Euler correction. -/
noncomputable def residueFunctional : residueDomain →ₗ[ℂ] ℂ :=
  stripResidueValue.comp
    ((LinearMap.snd ℂ (ℕ →₀ ℂ) (StripPoint →₀ ℂ)).comp
      (LinearEquiv.ofInjective residueDomainMap injective_residueDomainMap).symm.toLinearMap)

theorem residueFunctional_apply (fu : (ℕ →₀ ℂ) × (StripPoint →₀ ℂ))
    (h : residueDomainMap fu ∈ residueDomain) :
    residueFunctional ⟨residueDomainMap fu, h⟩ = stripResidueValue fu.2 := by
  have key : (LinearEquiv.ofInjective residueDomainMap injective_residueDomainMap).symm
      ⟨residueDomainMap fu, h⟩ = fu :=
    (LinearEquiv.symm_apply_eq _).mpr (Subtype.ext rfl)
  show stripResidueValue
    (((LinearEquiv.ofInjective residueDomainMap injective_residueDomainMap).symm)
      ⟨residueDomainMap fu, h⟩).2 = _
  rw [key]

theorem residueFunctional_of_eq {y : ℕ → ℂ} (hy : y ∈ residueDomain)
    (fu : (ℕ →₀ ℂ) × (StripPoint →₀ ℂ)) (h : residueDomainMap fu = y) :
    residueFunctional ⟨y, hy⟩ = stripResidueValue fu.2 := by
  subst h
  exact residueFunctional_apply fu hy

/-- The finitely supported prime fields:  the finite Euler corrections. -/
def finiteSupportSpace : Submodule ℂ (ℕ → ℂ) where
  carrier := {f | (Function.support f).Finite}
  add_mem' hf hg := (hf.union hg).subset (Function.support_add _ _)
  zero_mem' := by simp
  smul_mem' c f hf := Set.Finite.subset hf (by
    intro n hn
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hn ⊢
    intro h0
    exact hn (by rw [h0, mul_zero]))

theorem residueDomainMap_ofSupportFinite {f : ℕ → ℂ} (hf : (Function.support f).Finite) :
    residueDomainMap (Finsupp.ofSupportFinite f hf, 0) = f := by
  rw [residueDomainMap_apply]
  ext n
  simp [Finsupp.ofSupportFinite_coe, stripCharacterField]

theorem finiteSupportSpace_le_residueDomain : finiteSupportSpace ≤ residueDomain := by
  intro f hf
  have hf' : (Function.support f).Finite := hf
  exact ⟨(Finsupp.ofSupportFinite f hf', 0), residueDomainMap_ofSupportFinite hf'⟩

theorem residueFunctional_eq_zero_of_finiteSupport {f : ℕ → ℂ}
    (hf : f ∈ residueDomain) (hfin : (Function.support f).Finite) :
    residueFunctional ⟨f, hf⟩ = 0 := by
  rw [residueFunctional_of_eq hf (Finsupp.ofSupportFinite f hfin, 0)
    (residueDomainMap_ofSupportFinite hfin)]
  simp

theorem residueDomainMap_single (z : StripPoint) :
    residueDomainMap (0, Finsupp.single z 1) = primeShiftCharacter (z : ℂ) := by
  rw [residueDomainMap_apply, stripCharacterField]
  ext n
  simp [Finsupp.linearCombination_single]

theorem primeShiftCharacter_mem_residueDomain (z : StripPoint) :
    primeShiftCharacter (z : ℂ) ∈ residueDomain :=
  ⟨(0, Finsupp.single z 1), residueDomainMap_single z⟩

theorem residueFunctional_primeShiftCharacter (z : StripPoint)
    (hz : primeShiftCharacter (z : ℂ) ∈ residueDomain) :
    residueFunctional ⟨primeShiftCharacter (z : ℂ), hz⟩ = primeShiftResidue (z : ℂ) := by
  rw [residueFunctional_of_eq hz (0, Finsupp.single z 1) (residueDomainMap_single z)]
  rw [stripResidueValue, Finsupp.linearCombination_single]
  simp

/-! ## The closability criterion -/

/-- Closability of a densely defined functional on the vanishing-tail space:  every Marcinkiewicz
null sequence in the domain whose values converge has limit value zero. -/
def IsClosableMarcinkiewicz (D : Submodule ℂ (ℕ → ℂ)) (L : D →ₗ[ℂ] ℂ) : Prop :=
  ∀ (y : ℕ → D) (v : ℂ), TendstoMarcinkiewiczZero (fun n => (y n : ℕ → ℂ)) →
    Tendsto (fun n => L (y n)) atTop (𝓝 v) → v = 0

theorem memCriticalSummableLayer_absField_of_mem_residueDomain {y : ℕ → ℂ}
    (hy : y ∈ residueDomain) : MemCriticalSummableLayer (absField y) := by
  obtain ⟨⟨f, u⟩, rfl⟩ := hy
  rw [residueDomainMap_apply, stripCharacterField_eq_sum]
  refine memCriticalSummableLayer_absField_add ?_ ?_
  · exact memCriticalSummableLayer_of_finite_support f.support fun n hn => by
      simp [absField, Finsupp.notMem_support_iff.mp hn]
  · refine memCriticalSummableLayer_absField_finsetSum _ _ fun z _ => ?_
    exact memCriticalSummableLayer_absField_smul _
      (memCriticalSummableLayer_absField_primeShiftCharacter (stripPoint_half_lt_re z))

/-- **Finite Euler fields are dense in the residue domain.**  Every element of the domain is a
Marcinkiewicz limit of its own finite truncations. -/
theorem tendstoMarcinkiewiczZero_sub_primeFieldHead {y : ℕ → ℂ} (hy : y ∈ residueDomain) :
    TendstoMarcinkiewiczZero (fun n => y - primeFieldHead y n) := by
  have hM0 := memVanishingTailLayer_of_memCriticalSummableLayer
    (memCriticalSummableLayer_absField_of_mem_residueDomain hy)
  simpa only [sub_primeFieldHead] using tendstoMarcinkiewiczZero_tail hM0

/-- **Abstract graph lemma.**  A linear functional vanishing on a dense subspace of its domain is
closable exactly when it vanishes identically. -/
theorem eq_zero_of_isClosableMarcinkiewicz {D : Submodule ℂ (ℕ → ℂ)} {L : D →ₗ[ℂ] ℂ}
    (hclos : IsClosableMarcinkiewicz D L)
    (hC : finiteSupportSpace ≤ D)
    (hC0 : ∀ (f : ℕ → ℂ) (hf : f ∈ D), (Function.support f).Finite → L ⟨f, hf⟩ = 0)
    (hdense : ∀ y : ℕ → ℂ, y ∈ D → ∃ x : ℕ → (ℕ → ℂ),
      (∀ n, (Function.support (x n)).Finite) ∧ TendstoMarcinkiewiczZero (fun n => y - x n)) :
    ∀ (y : ℕ → ℂ) (hy : y ∈ D), L ⟨y, hy⟩ = 0 := by
  intro y hy
  obtain ⟨x, hxfin, htend⟩ := hdense y hy
  have hxD : ∀ n, x n ∈ D := fun n => hC (hxfin n)
  refine hclos (fun n => ⟨y - x n, D.sub_mem hy (hxD n)⟩) (L ⟨y, hy⟩) htend ?_
  have hconst : ∀ n, L ⟨y - x n, D.sub_mem hy (hxD n)⟩ = L ⟨y, hy⟩ := by
    intro n
    have hsub : (⟨y - x n, D.sub_mem hy (hxD n)⟩ : D) = ⟨y, hy⟩ - ⟨x n, hxD n⟩ := rfl
    rw [hsub, map_sub, hC0 (x n) (hxD n) (hxfin n), sub_zero]
  simp only [hconst]
  exact tendsto_const_nhds

theorem residueFunctional_eq_zero_iff_forall_residue :
    (∀ (y : ℕ → ℂ) (hy : y ∈ residueDomain), residueFunctional ⟨y, hy⟩ = 0) ↔
      ∀ z : StripPoint, primeShiftResidue (z : ℂ) = 0 := by
  constructor
  · intro h z
    rw [← residueFunctional_primeShiftCharacter z (primeShiftCharacter_mem_residueDomain z)]
    exact h _ _
  · intro h y hy
    obtain ⟨fu, hfu⟩ := id hy
    rw [residueFunctional_of_eq hy fu hfu, stripResidueValue_apply]
    exact Finset.sum_eq_zero fun z _ => by rw [h z, mul_zero]

/-- **The residue functional vanishes exactly under the Riemann hypothesis.** -/
theorem riemannHypothesis_iff_residueFunctional_eq_zero :
    RiemannHypothesis ↔
      ∀ (y : ℕ → ℂ) (hy : y ∈ residueDomain), residueFunctional ⟨y, hy⟩ = 0 := by
  rw [residueFunctional_eq_zero_iff_forall_residue]
  constructor
  · intro hRH z
    refine (primeShiftResidue_eq_zero_iff (stripPoint_ne_one z)).mpr ?_
    exact riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH _
      (stripPoint_half_lt_re z)
  · intro h
    refine riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr ?_
    intro s hlo hhi
    have hs : s ∈ RightStrip := ⟨hlo, hhi⟩
    exact (primeShiftResidue_eq_zero_iff (stripPoint_ne_one ⟨s, hs⟩)).mp (h ⟨s, hs⟩)

/-- **Prime-shift residue closability criterion.**  The canonical residue graph on the
vanishing-tail space is closable exactly when the Riemann hypothesis holds. -/
theorem riemannHypothesis_iff_residueFunctional_isClosable :
    RiemannHypothesis ↔ IsClosableMarcinkiewicz residueDomain residueFunctional := by
  constructor
  · intro hRH y v _ hval
    have hzero : ∀ n, residueFunctional (y n) = 0 := by
      intro n
      have hn := riemannHypothesis_iff_residueFunctional_eq_zero.mp hRH (y n) (y n).2
      simpa using hn
    simp only [hzero] at hval
    exact tendsto_nhds_unique hval tendsto_const_nhds
  · intro hclos
    refine riemannHypothesis_iff_residueFunctional_eq_zero.mpr ?_
    refine eq_zero_of_isClosableMarcinkiewicz hclos finiteSupportSpace_le_residueDomain
      (fun f hf hfin => residueFunctional_eq_zero_of_finiteSupport hf hfin) ?_
    intro y hy
    exact ⟨fun n => primeFieldHead y n, fun n => finite_support_primeFieldHead y n,
      tendstoMarcinkiewiczZero_sub_primeFieldHead hy⟩

/-- **The explicit nonclosability witness.**  A zero of `ζ` in the right strip supplies a sequence
of prime tails vanishing in the logarithmic Marcinkiewicz seminorm on which the residue functional
has the constant nonzero value `-m`. -/
theorem exists_marcinkiewicz_null_sequence_of_zetaZero {ρ : ℂ} (hρ : ρ ∈ RightStrip)
    (hzero : riemannZeta ρ = 0) :
    ∃ (x : ℕ → ℕ → ℂ) (hx : ∀ n, x n ∈ residueDomain),
      TendstoMarcinkiewiczZero x ∧
      (∀ n, residueFunctional ⟨x n, hx n⟩ = primeShiftResidue ρ) ∧
      primeShiftResidue ρ ≠ 0 := by
  classical
  set z : StripPoint := ⟨ρ, hρ⟩ with hz
  set x : ℕ → ℕ → ℂ := fun n => primeFieldTail (primeShiftCharacter ρ) n with hx
  have hxD : ∀ n, x n ∈ residueDomain := by
    intro n
    have hEq : x n = primeShiftCharacter ρ - primeFieldHead (primeShiftCharacter ρ) n := by
      rw [hx, sub_primeFieldHead]
    rw [hEq]
    exact Submodule.sub_mem _ (primeShiftCharacter_mem_residueDomain z)
      (finiteSupportSpace_le_residueDomain (finite_support_primeFieldHead _ n))
  refine ⟨x, hxD, ?_, ?_, ?_⟩
  · exact tendstoMarcinkiewiczZero_tail (memVanishingTailLayer_of_memCriticalSummableLayer
      (memCriticalSummableLayer_absField_primeShiftCharacter (stripPoint_half_lt_re z)))
  · intro n
    have hEq : x n = primeShiftCharacter ρ - primeFieldHead (primeShiftCharacter ρ) n := by
      rw [hx, sub_primeFieldHead]
    have hsplit : (⟨x n, hxD n⟩ : residueDomain)
        = ⟨primeShiftCharacter ρ, primeShiftCharacter_mem_residueDomain z⟩ -
          ⟨primeFieldHead (primeShiftCharacter ρ) n,
            finiteSupportSpace_le_residueDomain (finite_support_primeFieldHead _ n)⟩ :=
      Subtype.ext hEq
    rw [hsplit, map_sub,
      residueFunctional_primeShiftCharacter z (primeShiftCharacter_mem_residueDomain z),
      residueFunctional_eq_zero_of_finiteSupport _ (finite_support_primeFieldHead _ n), sub_zero]
  · intro hcon
    exact ((primeShiftResidue_eq_zero_iff (stripPoint_ne_one z)).mp hcon) hzero

end RHTower
