import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift
import GaloisForLFunctions.HTGeometry.CountableRelativeEntropyValue
import GaloisForLFunctions.HTGeometry.RamificationInformationChain

/-!
# Fresh reset versus deterministic return: the exact path defect

* **Lemma 2.1, `(RFDM.5)`–`(RFDM.6)`**: row-stochastic `K, L` with `KL = LK = I` are permutation
  matrices of mutually inverse bijections.
* **Corollary 2.2, `(RFDM.7)`**: on a reflection orbit `{x, Rx} × ℕ` the reset matrix is not a
  Markov isomorphism as soon as a recovery law has two positive atoms; the reset kernel never
  squares to the identity kernel.
* **Theorem 3.1, `(RFDM.8)`–`(RFDM.11)`**: for a probability vector `p` with diagonal coupling
  `Δ_p` and independent coupling `p ⊗ p`, `TV(Δ_p, p ⊗ p) = 1 - ∑ p_i²`,
  `D(Δ_p ‖ p ⊗ p) = H(p)` in extended relative entropy, `D(p ⊗ p ‖ Δ_p) = ∞` when `p` has two
  positive atoms, and the three defects vanish exactly at Dirac laws.
* **§5, `(RFDM.17)`–`(RFDM.18)`**: the swap `Φ(x, h₀, h₁) = (Rx, h₁, h₀)` is an involution carrying
  `κ_x ⊗ κ_{Rx}` to `κ_{Rx} ⊗ κ_x` and keeping the first history marginal `κ_x`.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResetDilation

/-! ### Lemma 2.1: a Markov isomorphism is a permutation -/

section MarkovIsomorphism

variable {H : Type*} [DecidableEq H] {K L : H → H → ℝ}

omit [DecidableEq H] in
theorem eq_zero_of_hasSum_zero_nonneg {f : H → ℝ} (h0 : ∀ i, 0 ≤ f i) (h : HasSum f 0) (i : H) :
    f i = 0 :=
  congrFun ((hasSum_zero_iff_of_nonneg h0).1 h) i

/-- A nonnegative row with total mass one, vanishing off `i`, is the point mass at `i`. -/
theorem row_eq_single {f : H → ℝ} (hf : HasSum f 1) (i : H) (hoff : ∀ j, j ≠ i → f j = 0)
    (j : H) : f j = if j = i then 1 else 0 := by
  have h := (hasSum_single i hoff).unique hf
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [hj, hoff j hj]

/-- **Lemma 2.1**: row-stochastic matrices with `KL = LK = I` are the permutation matrices of a
bijection and its inverse. -/
theorem markovIsomorphism_isPermutation (hK0 : ∀ i j, 0 ≤ K i j) (hL0 : ∀ i j, 0 ≤ L i j)
    (hK : ∀ i, HasSum (K i) 1) (hL : ∀ i, HasSum (L i) 1)
    (hKL : ∀ i j, HasSum (fun h => K i h * L h j) (if i = j then 1 else 0))
    (hLK : ∀ i j, HasSum (fun h => L i h * K h j) (if i = j then 1 else 0)) :
    ∃ φ : H ≃ H, (∀ i j, K i j = if j = φ i then 1 else 0) ∧
      ∀ j i, L j i = if i = φ.symm j then 1 else 0 := by
  classical
  -- a positive entry `K i h` forces row `h` of `L` to be the point mass at `i`
  have hrowL : ∀ i h, K i h ≠ 0 → ∀ j, L h j = if j = i then 1 else 0 := by
    intro i h hih j
    refine row_eq_single (hL h) i (fun j hj => ?_) j
    have hz : K i h * L h j = 0 := by
      have := hKL i j
      rw [if_neg (Ne.symm hj)] at this
      exact eq_zero_of_hasSum_zero_nonneg (fun g => mul_nonneg (hK0 i g) (hL0 g j)) this h
    exact (mul_eq_zero.1 hz).resolve_left hih
  -- every row of `K` has a positive entry
  have hex : ∀ i, ∃ h, K i h ≠ 0 := by
    intro i
    by_contra! hall
    have h0 : HasSum (K i) 0 := by
      have : K i = 0 := funext hall
      rw [this]; exact hasSum_zero
    exact one_ne_zero ((hK i).unique h0)
  choose φ hφ using hex
  -- row `i` of `K` is the point mass at `φ i`
  have hrowK : ∀ i j, K i j = if j = φ i then 1 else 0 := by
    intro i j
    have hLrow := hrowL i (φ i) (hφ i)
    have hfun : (fun g => L (φ i) g * K g j) = fun g => if g = i then K i j else 0 :=
      funext fun g => by
        rw [hLrow g]
        by_cases hg : g = i
        · subst hg; simp
        · simp [hg]
    have hsum : HasSum (fun g => L (φ i) g * K g j) (K i j) := by
      rw [hfun]; exact hasSum_ite_eq i (K i j)
    have h := hsum.unique (hLK (φ i) j)
    rw [h]
    by_cases hj : j = φ i
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  have hinj : Function.Injective φ := by
    intro i i' hii'
    by_contra hne
    have h1 := hrowL i (φ i) (hφ i) i
    have h2 := hrowL i' (φ i') (hφ i') i
    rw [if_pos rfl] at h1
    rw [← hii', if_neg hne] at h2
    rw [h1] at h2
    exact one_ne_zero h2
  have hsurj : Function.Surjective φ := by
    intro h'
    by_contra! hnot
    have hzero : ∀ g, L h' g * K g h' = 0 := fun g => by
      rw [hrowK g h', if_neg (fun h => hnot g h.symm), mul_zero]
    have h0 : HasSum (fun g => L h' g * K g h') 0 := by
      rw [show (fun g => L h' g * K g h') = 0 from funext hzero]; exact hasSum_zero
    have := (hLK h' h').unique h0
    rw [if_pos rfl] at this
    exact one_ne_zero this
  let e := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨e, fun i j => hrowK i j, fun j i => ?_⟩
  have hj : φ (e.symm j) = j := e.apply_symm_apply j
  have hrow := hrowL (e.symm j) (φ (e.symm j)) (hφ _) i
  rw [hj] at hrow
  exact hrow

end MarkovIsomorphism

/-! ### Corollary 2.2: the reset matrix on a reflection orbit -/

section Orbit

variable {X : Type*} [MeasurableSpace X] [DecidableEq X] (κ : Kernel X ℕ) [IsMarkovKernel κ]
  (R : X → X)

/-- The reflection orbit `O_x = {x, Rx}`. -/
abbrev reflectionOrbit (x : X) : Type _ := {y : X // y = x ∨ y = R x}

/-- The reset matrix `((y, n), (y', m)) ↦ 1_{y' = Ry} κ_{Ry}(m)` restricted to `O_x × ℕ`. -/
def orbitResetMatrix (x : X) (a b : reflectionOrbit R x × ℕ) : ℝ :=
  if (b.1 : X) = R a.1 then (κ (R a.1) {b.2}).toReal else 0

omit [IsMarkovKernel κ] in
theorem orbitResetMatrix_nonneg (x : X) (a b : reflectionOrbit R x × ℕ) :
    0 ≤ orbitResetMatrix κ R x a b := by
  unfold orbitResetMatrix
  split_ifs <;> simp

/-- **Corollary 2.2**: if a recovery law on the orbit has two positive atoms, the restricted reset
matrix admits no row-stochastic two-sided inverse. -/
theorem orbitReset_not_markovIsomorphism (hR : ∀ y, R (R y) = y) (x : X)
    (z : reflectionOrbit R x) {m₁ m₂ : ℕ} (hm : m₁ ≠ m₂) (h₁ : κ (z : X) {m₁} ≠ 0)
    (h₂ : κ (z : X) {m₂} ≠ 0)
    (hrows : ∀ a, HasSum (orbitResetMatrix κ R x a) 1) :
    ¬ ∃ L' : reflectionOrbit R x × ℕ → reflectionOrbit R x × ℕ → ℝ,
        (∀ a b, 0 ≤ L' a b) ∧ (∀ a, HasSum (L' a) 1) ∧
        (∀ a c, HasSum (fun b => orbitResetMatrix κ R x a b * L' b c)
          (if a = c then 1 else 0)) ∧
        (∀ a c, HasSum (fun b => L' a b * orbitResetMatrix κ R x b c)
          (if a = c then 1 else 0)) := by
  classical
  rintro ⟨L', hL0, hL, hKL, hLK⟩
  obtain ⟨φ, hK, -⟩ := markovIsomorphism_isPermutation (orbitResetMatrix_nonneg κ R x) hL0
    hrows hL hKL hLK
  -- the row above `y = R z` is `κ_z` on the fibre over `z`
  have hy : R (z : X) = x ∨ R (z : X) = R x := by
    rcases z.2 with hz | hz
    · right; rw [hz]
    · left; rw [hz, hR]
  let y : reflectionOrbit R x := ⟨R z, hy⟩
  have hRy : R (y : X) = z := hR z
  have hentry : ∀ m, orbitResetMatrix κ R x (y, 0) (z, m) = (κ (z : X) {m}).toReal := fun m => by
    rw [orbitResetMatrix, if_pos hRy.symm, hRy]
  have hpos : ∀ m, κ (z : X) {m} ≠ 0 → φ (y, 0) = (z, m) := fun m hmz => by
    have h := hK (y, 0) (z, m)
    rw [hentry] at h
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h
    exact hmz ((ENNReal.toReal_eq_zero_iff _).1 h |>.resolve_right (measure_ne_top _ _))
  have e₁ := hpos m₁ h₁
  have e₂ := hpos m₂ h₂
  rw [e₁] at e₂
  exact hm (Prod.ext_iff.1 e₂).2

omit [DecidableEq X] in
/-- **`(RFDM.7)`**: the reset lift never squares to the identity kernel, because it discards the
recovery coordinate. -/
theorem resetKernel_sq_ne_id [MeasurableSingletonClass X] [Nonempty X] (hRm : Measurable R) :
    formationLiftKernel κ R hRm ∘ₖ formationLiftKernel κ R hRm ≠ Kernel.id := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  have hL : formationLiftKernel κ R hRm (x, 0) = formationLiftKernel κ R hRm (x, 1) := by
    simp only [formationLiftKernel, Kernel.comp_apply, Kernel.deterministic_apply]
  have h01 : (formationLiftKernel κ R hRm ∘ₖ formationLiftKernel κ R hRm) (x, 0) =
      (formationLiftKernel κ R hRm ∘ₖ formationLiftKernel κ R hRm) (x, 1) := by
    rw [Kernel.comp_apply, Kernel.comp_apply, hL]
  rw [h, Kernel.id_apply, Kernel.id_apply] at h01
  have hm := congrArg (fun μ : Measure (X × ℕ) => μ {(x, 0)}) h01
  simp only [Measure.dirac_apply_of_mem (Set.mem_singleton (x, 0))] at hm
  rw [Measure.dirac_apply' _ (MeasurableSet.singleton _), Set.indicator_of_notMem (by simp)] at hm
  exact one_ne_zero hm

end Orbit

/-! ### Extended relative entropy between countable laws -/

section Countable

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  {Q P : Measure α}

omit [MeasurableSingletonClass α] in
theorem absolutelyContinuous_of_singleton (hac : ∀ a, P {a} = 0 → Q {a} = 0) : Q ≪ P := by
  refine Measure.AbsolutelyContinuous.mk fun S _ hS => ?_
  have hS' : S = ⋃ a ∈ S, ({a} : Set α) := by ext; simp
  rw [hS', measure_biUnion_null_iff (Set.to_countable S)]
  intro a ha
  exact hac a (measure_mono_null (Set.singleton_subset_iff.2 ha) hS)

theorem withDensity_singleton_ratio_of_ac [IsFiniteMeasure P]
    (hac : ∀ a, P {a} = 0 → Q {a} = 0) : P.withDensity (fun a => Q {a} / P {a}) = Q := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [withDensity_apply _ (MeasurableSet.singleton a), lintegral_singleton]
  by_cases hP : P {a} = 0
  · rw [hP, mul_zero, hac a hP]
  · exact ENNReal.div_mul_cancel hP (measure_ne_top P {a})

theorem llr_eq_log_singleton_ratio_of_ac [IsFiniteMeasure P]
    (hac : ∀ a, P {a} = 0 → Q {a} = 0) :
    llr Q P =ᵐ[Q] fun a => Real.log ((Q {a}).toReal / (P {a}).toReal) := by
  have hQP : Q ≪ P := absolutelyContinuous_of_singleton hac
  have hrn : Q.rnDeriv P =ᵐ[P] fun a => Q {a} / P {a} := by
    nth_rewrite 1 [← withDensity_singleton_ratio_of_ac (P := P) (Q := Q) hac]
    exact Measure.rnDeriv_withDensity P Measurable.of_discrete
  filter_upwards [hQP.ae_le hrn] with a ha
  rw [llr, ha, ENNReal.toReal_div]

/-- On a countable space, `D(Q ‖ P)` is the atom series when it converges absolutely. -/
theorem klDiv_countable_of_summable [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hac : ∀ a, P {a} = 0 → Q {a} = 0)
    (hsum : Summable fun a => (Q {a}).toReal * |Real.log ((Q {a}).toReal / (P {a}).toReal)|) :
    klDiv Q P = ENNReal.ofReal
      (∑' a, (Q {a}).toReal * Real.log ((Q {a}).toReal / (P {a}).toReal)) := by
  have hQP : Q ≪ P := absolutelyContinuous_of_singleton hac
  have hint : Integrable (fun a => Real.log ((Q {a}).toReal / (P {a}).toReal)) Q :=
    integrable_of_summable_singleton_weighted _ hsum
  have hllr := llr_eq_log_singleton_ratio_of_ac (Q := Q) hac
  rw [klDiv_of_ac_of_integrable hQP (hint.congr hllr.symm), integral_congr_ae hllr,
    integral_countable hint]
  simp [Measure.real, smul_eq_mul]

/-- On a countable space, `D(Q ‖ P) = ∞` when the atom series is not absolutely summable. -/
theorem klDiv_countable_of_not_summable [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hac : ∀ a, P {a} = 0 → Q {a} = 0)
    (hns : ¬ Summable fun a => (Q {a}).toReal * |Real.log ((Q {a}).toReal / (P {a}).toReal)|) :
    klDiv Q P = ⊤ := by
  refine klDiv_of_not_integrable fun hint => hns ?_
  have hllr := llr_eq_log_singleton_ratio_of_ac (Q := Q) hac
  exact summable_singleton_weighted_of_integrable (hint.congr hllr)

end Countable

/-! ### Theorem 3.1: diagonal/refresh separation -/

section Couplings

variable {H : Type*} [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]

/-- **`(RFDM.8)`** the diagonal coupling `Δ_p(i, j) = p_i 1_{i=j}`. -/
def diagonalCoupling (p : PMF H) : Measure (H × H) := p.toMeasure.map fun i => (i, i)

/-- **`(RFDM.8)`** the independent coupling `(p ⊗ p)(i, j) = p_i p_j`. -/
def productCoupling (p : PMF H) : Measure (H × H) := p.toMeasure.prod p.toMeasure

omit [MeasurableSingletonClass H] [Countable H] in
theorem measurable_diag : Measurable fun i : H => (i, i) := measurable_id.prodMk measurable_id

instance (p : PMF H) : IsProbabilityMeasure (diagonalCoupling p) :=
  Measure.isProbabilityMeasure_map measurable_diag.aemeasurable

instance (p : PMF H) : IsProbabilityMeasure (productCoupling p) := by
  unfold productCoupling; infer_instance

omit [Countable H] in
theorem diagonalCoupling_singleton [DecidableEq H] (p : PMF H) (i j : H) :
    diagonalCoupling p {(i, j)} = if i = j then p i else 0 := by
  rw [diagonalCoupling, Measure.map_apply measurable_diag (MeasurableSet.singleton _)]
  by_cases h : i = j
  · subst h
    have : (fun k : H => (k, k)) ⁻¹' {(i, i)} = {i} := by ext; simp
    rw [this, if_pos rfl, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  · have : (fun k : H => (k, k)) ⁻¹' {(i, j)} = ∅ := by
      ext k; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl; exact h
    rw [this, if_neg h, measure_empty]

theorem productCoupling_singleton (p : PMF H) (i j : H) :
    productCoupling p {(i, j)} = p i * p j := by
  rw [productCoupling, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]

/-- The real masses `p_i`. -/
def mass (p : PMF H) (i : H) : ℝ := (p i).toReal

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
theorem mass_nonneg (p : PMF H) (i : H) : 0 ≤ mass p i := ENNReal.toReal_nonneg

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
theorem mass_le_one (p : PMF H) (i : H) : mass p i ≤ 1 := by
  rw [mass, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one i)

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
theorem hasSum_mass (p : PMF H) : HasSum (mass p) 1 := by
  have hne : ∀ i, p i ≠ ⊤ := fun i => p.apply_ne_top i
  have hs : Summable (mass p) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have h := ENNReal.tsum_toReal_eq hne
  rw [p.tsum_coe, ENNReal.toReal_one] at h
  exact h ▸ hs.hasSum

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
theorem summable_mass_sq (p : PMF H) : Summable fun i => mass p i ^ 2 :=
  (hasSum_mass p).summable.of_nonneg_of_le (fun i => sq_nonneg _) fun i => by
    have := mass_le_one p i; have := mass_nonneg p i; nlinarith

/-- The real vector of `Δ_p`. -/
def diagonalVector (p : PMF H) (z : H × H) : ℝ := (diagonalCoupling p {z}).toReal

/-- The real vector of `p ⊗ p`. -/
def productVector (p : PMF H) (z : H × H) : ℝ := (productCoupling p {z}).toReal

omit [Countable H] in
theorem diagonalVector_apply [DecidableEq H] (p : PMF H) (i j : H) :
    diagonalVector p (i, j) = if i = j then mass p i else 0 := by
  rw [diagonalVector, diagonalCoupling_singleton]
  split_ifs <;> simp [mass]

theorem productVector_apply (p : PMF H) (i j : H) :
    productVector p (i, j) = mass p i * mass p j := by
  rw [productVector, productCoupling_singleton, ENNReal.toReal_mul, mass, mass]

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
/-- `∑_j |δ_{ij} - p_j| = 2(1 - p_i)`. -/
theorem tsum_abs_delta_sub_mass [DecidableEq H] (p : PMF H) (i : H) :
    HasSum (fun j => |(if i = j then (1 : ℝ) else 0) - mass p j|) (2 * (1 - mass p i)) := by
  have hs := hasSum_mass p
  have hsplit : (fun j => |(if i = j then (1 : ℝ) else 0) - mass p j|) =
      fun j => (if j = i then 1 - 2 * mass p i else 0) + mass p j := by
    funext j
    by_cases h : j = i
    · subst h
      rw [if_pos rfl, if_pos rfl, abs_of_nonneg (by linarith [mass_le_one p j])]
      ring
    · rw [if_neg (Ne.symm h), if_neg h, zero_sub, abs_neg, abs_of_nonneg (mass_nonneg p j),
        zero_add]
  rw [hsplit]
  have h1 := hasSum_ite_eq i (1 - 2 * mass p i)
  convert h1.add hs using 1
  ring

/-- **Theorem 3.1, `(RFDM.9)`**: `TV(Δ_p, p ⊗ p) = 1 - ∑ p_i²`. -/
theorem totalVariation_diagonal_product [DecidableEq H] (p : PMF H) :
    FormationExcess.totalVariation (diagonalVector p) (productVector p) =
      1 - ∑' i, mass p i ^ 2 := by
  have hrow : ∀ i, HasSum (fun j => |diagonalVector p (i, j) - productVector p (i, j)|)
      (mass p i * (2 * (1 - mass p i))) := fun i => by
    have h := (tsum_abs_delta_sub_mass p i).mul_left (mass p i)
    refine h.congr_fun fun j => ?_
    rw [diagonalVector_apply, productVector_apply]
    have hm := mass_nonneg p i
    by_cases hij : i = j
    · subst hij; simp only [if_true]
      rw [show mass p i - mass p i * mass p i = mass p i * (1 - mass p i) by ring, abs_mul,
        abs_of_nonneg hm]
    · simp only [hij, if_false]
      rw [show (0 : ℝ) - mass p i * mass p j = mass p i * (0 - mass p j) by ring, abs_mul,
        abs_of_nonneg hm]
  have hsumm : Summable fun z : H × H => |diagonalVector p z - productVector p z| := by
    refine (summable_prod_of_nonneg (fun _ => abs_nonneg _)).2 ⟨fun i => (hrow i).summable, ?_⟩
    simp_rw [fun i => (hrow i).tsum_eq]
    exact ((hasSum_mass p).mul_left 2).summable.sub ((summable_mass_sq p).mul_left 2) |>.congr
      fun i => by ring
  unfold FormationExcess.totalVariation
  rw [hsumm.tsum_prod]
  simp_rw [fun i => (hrow i).tsum_eq]
  have hA : ∑' i, mass p i * (2 * (1 - mass p i)) =
      2 * ∑' i, mass p i - 2 * ∑' i, mass p i ^ 2 := by
    rw [← tsum_mul_left, ← tsum_mul_left,
      ← ((hasSum_mass p).summable.mul_left 2).tsum_sub ((summable_mass_sq p).mul_left 2)]
    exact tsum_congr fun i => by ring
  rw [hA, (hasSum_mass p).tsum_eq]
  ring

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
/-- `∑ p_i² = 1` exactly for Dirac laws. -/
theorem tsum_mass_sq_eq_one_iff [DecidableEq H] (p : PMF H) :
    ∑' i, mass p i ^ 2 = 1 ↔ ∃ i, p = PMF.pure i := by
  constructor
  · intro h
    -- `∑ p_i(1 - p_i) = 0` with nonnegative terms forces every `p_i ∈ {0, 1}`
    have hz : ∑' i, mass p i * (1 - mass p i) = 0 := by
      have := ((hasSum_mass p).sub (summable_mass_sq p).hasSum).tsum_eq
      rw [h, sub_self] at this
      rw [← this]; exact tsum_congr fun i => by ring
    have hnn : ∀ i, 0 ≤ mass p i * (1 - mass p i) := fun i =>
      mul_nonneg (mass_nonneg p i) (by linarith [mass_le_one p i])
    have hs : Summable fun i => mass p i * (1 - mass p i) :=
      ((hasSum_mass p).summable.sub (summable_mass_sq p)).congr fun i => by ring
    have h01 : ∀ i, mass p i = 0 ∨ mass p i = 1 := fun i => by
      have := (hasSum_zero_iff_of_nonneg hnn).1 (hz ▸ hs.hasSum)
      have hi := congrFun this i
      rcases mul_eq_zero.1 hi with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    obtain ⟨i, hi⟩ : ∃ i, mass p i = 1 := by
      by_contra! hall
      have : mass p = 0 := funext fun i => (h01 i).resolve_right (hall i)
      have h1 := (hasSum_mass p).tsum_eq
      rw [this] at h1; simp at h1
    refine ⟨i, PMF.ext fun j => ?_⟩
    rw [PMF.pure_apply]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, ← ENNReal.ofReal_toReal (p.apply_ne_top j)]
      change ENNReal.ofReal (mass p j) = 1
      rw [hi, ENNReal.ofReal_one]
    · rw [if_neg hj]
      have hrest : mass p j = 0 := by
        have hsum := (hasSum_mass p)
        have hle : mass p i + mass p j ≤ 1 := by
          have := sum_le_hasSum ({i, j} : Finset H) (fun k _ => mass_nonneg p k) hsum
          rwa [Finset.sum_pair (Ne.symm hj)] at this
        linarith [mass_nonneg p j]
      have := (ENNReal.toReal_eq_zero_iff _).1 hrest
      exact this.resolve_right (p.apply_ne_top j)
  · rintro ⟨i, rfl⟩
    rw [tsum_eq_single i]
    · simp [mass, PMF.pure_apply]
    · intro j hj; simp [mass, PMF.pure_apply, hj]

/-- The diagonal Kullback--Leibler terms: off the diagonal they vanish; on it they are
`p_i log(1/p_i) = -p_i log p_i`. -/
theorem diagonal_kl_term [DecidableEq H] (p : PMF H) (i j : H) :
    (diagonalCoupling p {(i, j)}).toReal *
        Real.log ((diagonalCoupling p {(i, j)}).toReal / (productCoupling p {(i, j)}).toReal) =
      if i = j then Real.negMulLog (mass p i) else 0 := by
  have hd := diagonalVector_apply p i j
  have hpr := productVector_apply p i j
  unfold diagonalVector at hd
  unfold productVector at hpr
  rw [hd, hpr]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, Real.negMulLog]
    by_cases h0 : mass p i = 0
    · simp [h0]
    · rw [show mass p i / (mass p i * mass p i) = (mass p i)⁻¹ by field_simp, Real.log_inv]
      ring
  · simp [hij]

theorem diagonal_kl_absTerm [DecidableEq H] (p : PMF H) (i j : H) :
    (diagonalCoupling p {(i, j)}).toReal *
        |Real.log ((diagonalCoupling p {(i, j)}).toReal / (productCoupling p {(i, j)}).toReal)| =
      if i = j then Real.negMulLog (mass p i) else 0 := by
  have hd := diagonalVector_apply p i j
  have hpr := productVector_apply p i j
  unfold diagonalVector at hd
  unfold productVector at hpr
  rw [hd, hpr]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, Real.negMulLog]
    by_cases h0 : mass p i = 0
    · simp [h0]
    · have hpos : 0 < mass p i := lt_of_le_of_ne (mass_nonneg p i) (Ne.symm h0)
      rw [show mass p i / (mass p i * mass p i) = (mass p i)⁻¹ by field_simp, Real.log_inv,
        abs_neg, abs_of_nonpos (Real.log_nonpos hpos.le (mass_le_one p i))]
      ring
  · simp [hij]

theorem productCoupling_ac (p : PMF H) :
    ∀ z, productCoupling p {z} = 0 → diagonalCoupling p {z} = 0 := by
  classical
  rintro ⟨i, j⟩ h
  rw [productCoupling_singleton] at h
  rw [diagonalCoupling_singleton]
  split_ifs with hij
  · subst hij
    rcases mul_eq_zero.1 h with h | h <;> exact h
  · rfl

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
theorem summable_diagonal_iff [DecidableEq H] {f : H × H → ℝ} (p : PMF H)
    (hf : ∀ i j, f (i, j) = if i = j then Real.negMulLog (mass p i) else 0) :
    Summable f ↔ Summable fun i => Real.negMulLog (mass p i) := by
  have hinj : Function.Injective fun i : H => (i, i) := fun a b h => (Prod.ext_iff.1 h).1
  rw [← hinj.summable_iff (fun z hz => ?_)]
  · exact Iff.of_eq (congrArg Summable (funext fun i => by simp [hf]))
  · obtain ⟨i, j⟩ := z
    rw [hf, if_neg]
    rintro rfl; exact hz ⟨i, rfl⟩

/-- **Theorem 3.1, `(RFDM.10)`**: `D(Δ_p ‖ p ⊗ p) = H(p) = ∑ -p_i log p_i` in `[0, ∞]`. -/
theorem klDiv_diagonal_product [DecidableEq H] (p : PMF H) :
    klDiv (diagonalCoupling p) (productCoupling p) =
      ∑' i, ENNReal.ofReal (Real.negMulLog (mass p i)) := by
  have hinj : Function.Injective fun i : H => (i, i) := fun a b h => (Prod.ext_iff.1 h).1
  have hnn : ∀ i, 0 ≤ Real.negMulLog (mass p i) := fun i =>
    Real.negMulLog_nonneg (mass_nonneg p i) (mass_le_one p i)
  have habs := summable_diagonal_iff (f := fun z : H × H => (diagonalCoupling p {z}).toReal *
      |Real.log ((diagonalCoupling p {z}).toReal / (productCoupling p {z}).toReal)|) p
    (fun i j => diagonal_kl_absTerm p i j)
  by_cases hs : Summable fun i => Real.negMulLog (mass p i)
  · rw [klDiv_countable_of_summable (productCoupling_ac p) (habs.2 hs),
      ← ENNReal.ofReal_tsum_of_nonneg hnn hs]
    congr 1
    have hterm : (fun z : H × H => (diagonalCoupling p {z}).toReal *
        Real.log ((diagonalCoupling p {z}).toReal / (productCoupling p {z}).toReal)) =
        fun z => if z.1 = z.2 then Real.negMulLog (mass p z.1) else 0 := by
      funext z; obtain ⟨i, j⟩ := z; exact diagonal_kl_term p i j
    rw [hterm, ← hinj.tsum_eq (f := fun z : H × H => if z.1 = z.2 then
        Real.negMulLog (mass p z.1) else 0)]
    · simp
    · intro z hz
      obtain ⟨i, j⟩ := z
      by_contra hr
      apply hz
      simp only [if_neg (fun h : i = j => hr ⟨i, by rw [h]⟩)]
  · rw [klDiv_countable_of_not_summable (productCoupling_ac p) (fun h => hs (habs.1 h))]
    symm
    by_contra hne
    exact hs ((ENNReal.summable_toReal hne).congr fun i =>
      ENNReal.toReal_ofReal (hnn i))

/-- **Theorem 3.1, `(RFDM.11)`**: `D(p ⊗ p ‖ Δ_p) = ∞` when `p` has two positive atoms. -/
theorem klDiv_product_diagonal_eq_top [DecidableEq H] (p : PMF H) {i j : H} (hij : i ≠ j)
    (hi : p i ≠ 0) (hj : p j ≠ 0) : klDiv (productCoupling p) (diagonalCoupling p) = ⊤ := by
  refine klDiv_of_not_ac fun hac => ?_
  have h0 : diagonalCoupling p {(i, j)} = 0 := by rw [diagonalCoupling_singleton, if_neg hij]
  have := hac h0
  rw [productCoupling_singleton] at this
  exact mul_ne_zero hi hj this

omit [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
/-- A law with at most one positive atom is Dirac. -/
theorem exists_two_atoms_of_not_dirac (p : PMF H) (hp : ¬ ∃ i, p = PMF.pure i) :
    ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra! h
    have := p.tsum_coe
    simp [h] at this
  refine ⟨i, ?_⟩
  by_contra! hall
  apply hp
  refine ⟨i, PMF.ext fun j => ?_⟩
  rw [PMF.pure_apply]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl]
    have hsum := p.tsum_coe
    rw [tsum_eq_single j (fun k hk => hall k (Ne.symm hk) hi)] at hsum
    exact hsum
  · rw [if_neg hj]
    exact hall j (Ne.symm hj) hi

/-- **Theorem 3.1**: the three defects vanish exactly at Dirac laws. -/
theorem diagonal_defects_vanish_iff [DecidableEq H] (p : PMF H) :
    (FormationExcess.totalVariation (diagonalVector p) (productVector p) = 0 ↔
        ∃ i, p = PMF.pure i) ∧
      (klDiv (diagonalCoupling p) (productCoupling p) = 0 ↔ ∃ i, p = PMF.pure i) ∧
      (klDiv (productCoupling p) (diagonalCoupling p) = 0 ↔ ∃ i, p = PMF.pure i) := by
  have hdirac : ∀ i, p = PMF.pure i → diagonalCoupling p = productCoupling p := by
    rintro i rfl
    refine Measure.ext_of_singleton fun z => ?_
    obtain ⟨a, b⟩ := z
    rw [diagonalCoupling_singleton, productCoupling_singleton]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = i
      · subst ha; simp
      · simp [PMF.pure_apply, ha]
    · rw [if_neg hab]
      by_cases ha : a = i
      · subst ha; simp [PMF.pure_apply, Ne.symm hab]
      · simp [PMF.pure_apply, ha]
  refine ⟨by rw [totalVariation_diagonal_product, sub_eq_zero, eq_comm, tsum_mass_sq_eq_one_iff],
    ⟨fun h => ?_, fun ⟨i, hi⟩ => by rw [hdirac i hi, klDiv_self]⟩,
    ⟨fun h => ?_, fun ⟨i, hi⟩ => by rw [hdirac i hi, klDiv_self]⟩⟩
  · by_contra hp
    obtain ⟨i, j, hij, hi, hj⟩ := exists_two_atoms_of_not_dirac p hp
    rw [klDiv_diagonal_product, ENNReal.tsum_eq_zero] at h
    have hzero : ∀ k, p k ≠ 0 → p k = 1 := fun k hk => by
      have h1 := h k
      rw [ENNReal.ofReal_eq_zero] at h1
      have hm0 := mass_nonneg p k
      have hm1 := mass_le_one p k
      have hpos : 0 < mass p k := by
        rw [mass, ENNReal.toReal_pos_iff]
        exact ⟨pos_iff_ne_zero.2 hk, (p.apply_ne_top k).lt_top⟩
      have hle := Real.negMulLog_nonneg hm0 hm1
      have h0 : Real.negMulLog (mass p k) = 0 := le_antisymm h1 hle
      rw [Real.negMulLog, neg_mul, neg_eq_zero, mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 hpos.ne'
      · rcases Real.log_eq_zero.1 h0 with h0 | h0 | h0
        · exact absurd h0 hpos.ne'
        · rw [← ENNReal.ofReal_toReal (p.apply_ne_top k)]
          change ENNReal.ofReal (mass p k) = 1
          rw [h0, ENNReal.ofReal_one]
        · linarith
    have hsum := sum_le_hasSum ({i, j} : Finset H) (fun k _ => mass_nonneg p k) (hasSum_mass p)
    rw [Finset.sum_pair hij] at hsum
    have hi1 : mass p i = 1 := by simp [mass, hzero i hi]
    have hj1 : mass p j = 1 := by simp [mass, hzero j hj]
    linarith
  · by_contra hp
    obtain ⟨i, j, hij, hi, hj⟩ := exists_two_atoms_of_not_dirac p hp
    rw [klDiv_product_diagonal_eq_top p hij hi hj] at h
    exact ENNReal.top_ne_zero h

end Couplings

/-! ### §5: finite enlargements fix one-time marginals but not the path law -/

section Swap

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H] (κ : Kernel X H) [IsMarkovKernel κ]
  (R : X → X)

/-- **`(RFDM.17)`** `Φ(x, h₀, h₁) = (Rx, h₁, h₀)`. -/
def historySwap (w : X × H × H) : X × H × H := (R w.1, w.2.2, w.2.1)

/-- **`(RFDM.17)`** `κ̃_x = κ_x ⊗ κ_{Rx}`. -/
def doubledRecovery (x : X) : Measure (H × H) := (κ x).prod (κ (R x))

/-- **`(RFDM.18)`** `Φ² = I`, `Φ_* κ̃_x = κ̃_{Rx}`, and the first history marginal of `κ̃_x` is
`κ_x`, so every one-time packet conditional is correct; after two steps the first coordinate is
the original `h₀` rather than a fresh sample. -/
theorem historySwap_laws (hR : ∀ x, R (R x) = x) (x : X) :
    (∀ w : X × H × H, historySwap R (historySwap R w) = w) ∧
      (doubledRecovery κ R x).map Prod.swap = doubledRecovery κ R (R x) ∧
      (doubledRecovery κ R x).map Prod.fst = κ x := by
  refine ⟨fun w => ?_, ?_, ?_⟩
  · obtain ⟨x, h₀, h₁⟩ := w
    simp [historySwap, hR]
  · rw [doubledRecovery, doubledRecovery, Measure.prod_swap, hR]
  · rw [doubledRecovery, Measure.map_fst_prod, measure_univ, one_smul]

end Swap

end GaloisForLFunctions.HTGeometry.ResetDilation
