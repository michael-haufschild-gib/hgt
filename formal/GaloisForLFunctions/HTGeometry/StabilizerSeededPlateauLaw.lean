/-
# The stabilizer-seeded fixed-shell plateau

The stabilizer family is chosen once, before any eigenbasis, so the exact two-design collision law
holds against *every* orthonormal family at the same states.  Combining it with the fixed-shell
plateau bookkeeping gives the all-late common-time bound at the full Hilbert-dimension collision
scale `2L/(D+1)` rather than the product-input scale `(2/3)^n`.

Main results:
* `limsup_add_le_atTop`, `limsup_finsetSum_le` — finite subadditivity of an upper limit.
* `exists_stabilizer_family_collision_eq` — the two-design law with the family chosen first.
* `limsup_sphereLaw_stabilizerCapture_le` — **`(13)`: the per-seed plateau bound**.
* `limsup_sphereLaw_stabilizerSeeded_sum_le` — **`(11)`: the seed-averaged plateau bound**.
-/
import GaloisForLFunctions.HTGeometry.PauliChainPlateauLaw
import GaloisForLFunctions.HTGeometry.StabilizerCollisionMarkov

open Filter Topology MeasureTheory Metric Matrix Finset

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Finite subadditivity of an upper limit -/

theorem limsup_add_le_atTop (u v : ℝ → ENNReal) :
    atTop.limsup (fun t => u t + v t) ≤ atTop.limsup u + atTop.limsup v := by
  by_cases hu : atTop.limsup u = ⊤
  · simp [hu]
  by_cases hv : atTop.limsup v = ⊤
  · simp [hv]
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro η hη _
  have hu' : ∀ᶠ t in atTop, u t < atTop.limsup u + (η : ENNReal) / 2 := by
    refine Filter.eventually_lt_of_limsup_lt ?_
    exact ENNReal.lt_add_right hu (by simp [hη.ne'])
  have hv' : ∀ᶠ t in atTop, v t < atTop.limsup v + (η : ENNReal) / 2 := by
    refine Filter.eventually_lt_of_limsup_lt ?_
    exact ENNReal.lt_add_right hv (by simp [hη.ne'])
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hu', hv'] with t htu htv
  calc u t + v t ≤ (atTop.limsup u + (η : ENNReal) / 2)
        + (atTop.limsup v + (η : ENNReal) / 2) := add_le_add htu.le htv.le
    _ = atTop.limsup u + atTop.limsup v + ((η : ENNReal) / 2 + (η : ENNReal) / 2) := by ring
    _ = atTop.limsup u + atTop.limsup v + (η : ENNReal) := by
        rw [ENNReal.add_halves]

theorem limsup_finsetSum_le {ι : Type*} (T : Finset ι) (u : ι → ℝ → ENNReal) :
    atTop.limsup (fun t => ∑ q ∈ T, u q t) ≤ ∑ q ∈ T, atTop.limsup (u q) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert q T hq ih =>
      rw [Finset.sum_insert hq]
      have hcong : atTop.limsup (fun t => ∑ p ∈ insert q T, u p t)
          = atTop.limsup (fun t => u q t + ∑ p ∈ T, u p t) := by
        refine Filter.limsup_congr (Filter.Eventually.of_forall fun t => ?_)
        rw [Finset.sum_insert hq]
      rw [hcong]
      exact le_trans (limsup_add_le_atTop (u q) (fun t => ∑ p ∈ T, u p t))
        (add_le_add le_rfl ih)

/-! ## The stabilizer family, chosen before any eigenbasis -/

variable {n : ℕ}

/-- **The exact two-design collision law with the stabilizer family chosen first.**  One family of
stabilizer states works against *every* orthonormal family at once. -/
theorem exists_stabilizer_family_collision_eq (n : ℕ) :
    ∃ χ : (Fin n → PauliSymp n) → (Fin n → ZMod 2) →
        (FiniteQubitConfiguration (Fin n) → ℂ),
      (∀ b ∈ lagrBases n, ∀ ε, (∑ x, ‖χ b ε x‖ ^ 2) = 1) ∧
      ∀ e : FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ,
        (∀ j, (∑ x, ‖e j x‖ ^ 2) = 1) →
        ((2 : ℝ) ^ n + 1) * (∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
            ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2) =
          ((lagrBases n).card : ℝ) * 2 ^ (n + 1) := by
  classical
  choose! χ hunitχ hdiag using fun (b : Fin n → PauliSymp n) (hbasis : IsLagrBasis b)
    (ε : Fin n → ZMod 2) => exists_stabilizer_pure_state hbasis ε
  refine ⟨χ, fun b hb ε => hunitχ b (mem_lagrBases.mp hb) ε, ?_⟩
  intro e hunit
  have hcomplex := sum_lagrBases_sign_collision e hunit
  have hterm : ∀ b ∈ lagrBases n, (∑ ε : Fin n → ZMod 2,
      ∑ j, (matDiag (stabProjectorOf b ε) (e j)) ^ 2) =
      ((∑ ε : Fin n → ZMod 2,
        ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2 : ℝ) : ℂ) := by
    intro b hb
    have hbasis := mem_lagrBases.mp hb
    push_cast
    refine Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun j _ => ?_
    rw [stabProjectorOf_eq hbasis.1, hdiag b hbasis ε (e j)]
  rw [Finset.sum_congr rfl hterm] at hcomplex
  have hcast : (((2 : ℝ) ^ n + 1 : ℝ) : ℂ) *
      ((∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
        ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2 : ℝ) : ℂ) =
      ((((lagrBases n).card : ℝ) * 2 ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    push_cast at hcomplex
    rw [← hcomplex]
  exact_mod_cast hcast

/-! ## The plateau bound at a fixed seed -/

theorem sum_normSq_of_inner_one {α : Type*} [Fintype α] {u : α → ℂ}
    (h : finiteComplexInner u u = 1) : ∑ x, ‖u x‖ ^ 2 = 1 := by
  have hcast : finiteComplexInner u u = ((∑ x, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [hcast] at h
  exact_mod_cast h

/-- **`(13)`: the plateau bound at a fixed seed.**  For any unit input state, the long-time shell
density of the directions whose evolution reaches the dictionary is at most `2^{-r/2}` plus the
shell mass of the directions with a large input collision. -/
theorem limsup_sphereLaw_seedCapture_le (k : ℕ) {C : Type*} [Fintype C] [Nonempty C]
    (i₀ : Fin (2 ^ (k + 3)))
    (Z : C → (Fin (2 ^ (k + 3)) → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    (Om : Fin (2 ^ (k + 3)) → ℂ) (hOm : finiteComplexInner Om Om = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (atTop.limsup fun t : ℝ => (sphereLaw (Fintype.card (ChainLabel (k + 3))))
        {x | ∃ κ : C, a ≤ finitePureStateFidelity
          (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
            (2 * Real.pi * t) *ᵥ Om) (Z κ)})
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
        + (sphereLaw (Fintype.card (ChainLabel (k + 3))))
            (goodSet (chainPauliFin_isHermitian (k + 3)) Om c₀)ᶜ := by
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  have hdisc := spectralDiscriminantPoly_chainPauliFin_succ_ne_zero k
  have hRL : ∀ b : Fin (2 ^ (k + 3)) → ℝ, (∑ i, b i = 0) → b ≠ 0 →
      ∀ g : coeffSphere (Fintype.card (ChainLabel (k + 3))) → ℂ, Measurable g →
        ∀ Cb : ℝ, 0 ≤ Cb → (∀ x, ‖g x‖ ≤ Cb) →
        Tendsto (fun u : ℝ => ∫ x, g x *
            Complex.exp (-((u * sortedSpectralAction (chainPauliFin_isHermitian (k + 3)) b
              (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ
              (Fin (Fintype.card (ChainLabel (k + 3)))))).toSphere)) (cocompact ℝ) (nhds 0) :=
    fun b hbsum hbne g hg Cb hC0 hC =>
      tendsto_integral_exp_sortedSpectralAction_zero_pauliChain k b hbsum hbne g hg hC0 hC
  exact limsup_sphereLaw_capture_le hN (chainPauliFin_isHermitian (k + 3)) hdisc hRL i₀ Om hOm
    Z hZ ha hr hscale hM hcard hs
    (measurableSet_goodSet (chainPauliFin_isHermitian (k + 3)) Om c₀)
    (fun x hx => hx.1)
    (fun x hx => by rw [← crossCollision_eq (chainPauliFin_isHermitian (k + 3)) Om hx.1]; exact hx.2)
    le_rfl

/-! ## The seed-averaged plateau bound -/

/-- The index set of the stabilizer family: a Lagrangian basis and a sign vector. -/
def stabIndex (n : ℕ) : Finset ((Fin n → PauliSymp n) × (Fin n → ZMod 2)) :=
  (lagrBases n) ×ˢ (Finset.univ : Finset (Fin n → ZMod 2))

theorem card_stabIndex (n : ℕ) :
    (stabIndex n).card = (lagrBases n).card * 2 ^ n := by
  rw [stabIndex, Finset.card_product, Finset.card_univ]
  congr 1
  simp

/-- A stabilizer seed read on the numbered register. -/
def stabSeed (n : ℕ)
    (χ : (Fin n → PauliSymp n) → (Fin n → ZMod 2) → (FiniteQubitConfiguration (Fin n) → ℂ))
    (q : (Fin n → PauliSymp n) × (Fin n → ZMod 2)) : Fin (2 ^ n) → ℂ :=
  fun m => χ q.1 q.2 ((qubitConfigFin n).symm m)

theorem stabSeed_comp (n : ℕ)
    (χ : (Fin n → PauliSymp n) → (Fin n → ZMod 2) → (FiniteQubitConfiguration (Fin n) → ℂ))
    (q : (Fin n → PauliSymp n) × (Fin n → ZMod 2)) :
    (fun y => stabSeed n χ q ((qubitConfigFin n) y)) = χ q.1 q.2 := by
  funext y
  show χ q.1 q.2 ((qubitConfigFin n).symm ((qubitConfigFin n) y)) = χ q.1 q.2 y
  rw [Equiv.symm_apply_apply]

theorem finiteComplexInner_stabSeed (n : ℕ)
    {χ : (Fin n → PauliSymp n) → (Fin n → ZMod 2) → (FiniteQubitConfiguration (Fin n) → ℂ)}
    {q : (Fin n → PauliSymp n) × (Fin n → ZMod 2)} (hq : (∑ x, ‖χ q.1 q.2 x‖ ^ 2) = 1) :
    finiteComplexInner (stabSeed n χ q) (stabSeed n χ q) = 1 := by
  have hs1 : ∑ m, ‖stabSeed n χ q m‖ ^ 2 = 1 := by
    rw [← hq]
    exact Equiv.sum_comp (qubitConfigFin n).symm (fun y => ‖χ q.1 q.2 y‖ ^ 2)
  have hcast : finiteComplexInner (stabSeed n χ q) (stabSeed n χ q)
      = ((∑ m, ‖stabSeed n χ q m‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [hcast, hs1]
  norm_num

/-- The eigenbasis of the shell Hamiltonian read on the register. -/
def registerEigenBasis (n : ℕ) {N : ℕ} {P : Fin N → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (x : coeffSphere N) :
    FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ :=
  fun j y => sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j) (qubitConfigFin n y)

theorem sum_normSq_registerEigenBasis (n : ℕ) {N : ℕ}
    {P : Fin N → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (x : coeffSphere N) (j : FiniteQubitConfiguration (Fin n)) :
    (∑ y, ‖registerEigenBasis n hP x j y‖ ^ 2) = 1 := by
  have heb := isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x)
  have h1 : finiteComplexInner (sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j))
      (sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j)) = 1 := by
    rw [heb.orth (qubitConfigFin n j) (qubitConfigFin n j), if_pos rfl]
  show (∑ y, ‖sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j)
      (qubitConfigFin n y)‖ ^ 2) = 1
  rw [Equiv.sum_comp (qubitConfigFin n)
    (fun m => ‖sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j) m‖ ^ 2)]
  exact sum_normSq_of_inner_one h1

theorem crossCollision_stabSeed (k : ℕ)
    (χ : (Fin (k + 3) → PauliSymp (k + 3)) → (Fin (k + 3) → ZMod 2) →
      (FiniteQubitConfiguration (Fin (k + 3)) → ℂ))
    (q : (Fin (k + 3) → PauliSymp (k + 3)) × (Fin (k + 3) → ZMod 2))
    {x : coeffSphere (Fintype.card (ChainLabel (k + 3)))}
    (hx : x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3))) :
    crossCollision (chainPauliFin_isHermitian (k + 3)) (stabSeed (k + 3) χ q) x
      = ∑ j, (finitePureStateFidelity
          (registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x j)
          (χ q.1 q.2)) ^ 2 := by
  rw [crossCollision_eq (chainPauliFin_isHermitian (k + 3)) (stabSeed (k + 3) χ q) hx]
  rw [← spectralCollision_reindexBasis (qubitConfigFin (k + 3))
    (sortedEigenBasis (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x))
    (stabSeed (k + 3) χ q)]
  rw [stabSeed_comp]
  rfl

/-- **`(11)`: the seed-averaged plateau bound.**  Summed over the stabilizer seeds, the long-time
shell density of the directions whose evolution reaches the dictionary is at most
`|Stab| (2^{-r/2} + 1/L)`. -/
theorem limsup_sphereLaw_stabilizerSeeded_sum_le (k : ℕ) {C : Type*} [Fintype C] [Nonempty C]
    (i₀ : Fin (2 ^ (k + 3)))
    (Z : C → (Fin (2 ^ (k + 3)) → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : 0 < L)
    (hscale : 16 * (2 * L / ((2 : ℝ) ^ (k + 3) + 1)) / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    ∃ χ : (Fin (k + 3) → PauliSymp (k + 3)) → (Fin (k + 3) → ZMod 2) →
        (FiniteQubitConfiguration (Fin (k + 3)) → ℂ),
      (∀ b ∈ lagrBases (k + 3), ∀ ε, (∑ x, ‖χ b ε x‖ ^ 2) = 1) ∧
      (atTop.limsup fun t : ℝ => ∑ q ∈ stabIndex (k + 3),
            (sphereLaw (Fintype.card (ChainLabel (k + 3))))
              {x | ∃ κ : C, a ≤ finitePureStateFidelity
                (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
                  (2 * Real.pi * t) *ᵥ stabSeed (k + 3) χ q) (Z κ)})
        ≤ ((stabIndex (k + 3)).card : ENNReal)
            * ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
          + ((stabIndex (k + 3)).card : ENNReal) * ENNReal.ofReal (1 / L) := by
  classical
  obtain ⟨χ, hunit, hdesign⟩ := exists_stabilizer_family_collision_eq (k + 3)
  refine ⟨χ, hunit, ?_⟩
  refine le_trans (limsup_finsetSum_le (stabIndex (k + 3)) (fun q t =>
    (sphereLaw (Fintype.card (ChainLabel (k + 3))))
      {x | ∃ κ : C, a ≤ finitePureStateFidelity
        (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
          (2 * Real.pi * t) *ᵥ stabSeed (k + 3) χ q) (Z κ)})) ?_
  obtain ⟨hPP, hPPdef⟩ : ∃ hPP, hPP = chainPauliFin_isHermitian (k + 3) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = 2 * L / ((2 : ℝ) ^ (k + 3) + 1) := ⟨_, rfl⟩
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  haveI := isProbabilityMeasure_sphereLaw hN
  have hper : ∀ q ∈ stabIndex (k + 3),
      (atTop.limsup fun t : ℝ => (sphereLaw (Fintype.card (ChainLabel (k + 3))))
        {x | ∃ κ : C, a ≤ finitePureStateFidelity
          (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
            (2 * Real.pi * t) *ᵥ stabSeed (k + 3) χ q) (Z κ)})
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
          + (sphereLaw (Fintype.card (ChainLabel (k + 3))))
              (goodSet hPP (stabSeed (k + 3) χ q) c₀)ᶜ := by
    intro q hq
    rw [stabIndex, Finset.mem_product] at hq
    rw [hPPdef]
    exact limsup_sphereLaw_seedCapture_le k i₀ Z hZ (stabSeed (k + 3) χ q)
      (finiteComplexInner_stabSeed (k + 3) (hunit q.1 hq.1 q.2)) ha hr
      (by rw [hc₀def]; exact hscale) hM hcard hs
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  refine add_le_add le_rfl ?_
  obtain ⟨badSet, hbadDef⟩ : ∃ badSet : ((Fin (k + 3) → PauliSymp (k + 3)) ×
      (Fin (k + 3) → ZMod 2)) → Set (coeffSphere (Fintype.card (ChainLabel (k + 3)))),
      badSet = fun q => simpleLocus hPP ∩
        crossCollision hPP (stabSeed (k + 3) χ q) ⁻¹' Set.Ioi c₀ := ⟨_, rfl⟩
  have hbadmeas : ∀ q, MeasurableSet (badSet q) := by
    intro q
    rw [hbadDef]
    exact ((continuousOn_crossCollision hPP (stabSeed (k + 3) χ q)).isOpen_inter_preimage
      (isOpen_simpleLocus hPP) isOpen_Ioi).measurableSet
  have hSnull : (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (simpleLocus hPP)ᶜ = 0 := by
    have hcompl : (simpleLocus hPP)ᶜ = sphereCoeff ⁻¹' {θ |
        ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hPP θ).eigenvalues} := rfl
    rw [hcompl, hPPdef]
    exact sphereLaw_eq_zero_of_toSphere_eq_zero
      (toSphere_degenerate_eq_zero (chainPauliFin_isHermitian (k + 3))
        (spectralDiscriminantPoly_chainPauliFin_succ_ne_zero k))
  have hstep : ∀ q ∈ stabIndex (k + 3),
      (sphereLaw (Fintype.card (ChainLabel (k + 3))))
          (goodSet hPP (stabSeed (k + 3) χ q) c₀)ᶜ
        ≤ (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (badSet q) := by
    intro q _
    have hsub : (goodSet hPP (stabSeed (k + 3) χ q) c₀)ᶜ ⊆ (simpleLocus hPP)ᶜ ∪ badSet q := by
      intro x hx
      by_cases hxs : x ∈ simpleLocus hPP
      · refine Or.inr ?_
        rw [hbadDef]
        refine ⟨hxs, ?_⟩
        show c₀ < crossCollision hPP (stabSeed (k + 3) χ q) x
        by_contra hle
        exact hx ⟨hxs, not_lt.mp hle⟩
      · exact Or.inl hxs
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [hSnull, zero_add]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hind : ∀ q, (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (badSet q)
      = ∫⁻ x, Set.indicator (badSet q)
          (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x
        ∂(sphereLaw (Fintype.card (ChainLabel (k + 3)))) :=
    fun q => (lintegral_indicator_one (hbadmeas q)).symm
  rw [Finset.sum_congr rfl (fun q _ => hind q), ← lintegral_finsetSum]
  · refine le_trans (lintegral_mono
      (g := fun _ => ((stabIndex (k + 3)).card : ENNReal) * ENNReal.ofReal (1 / L)) ?_) ?_
    · intro x
      show (∑ q ∈ stabIndex (k + 3), Set.indicator (badSet q)
          (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x)
        ≤ ((stabIndex (k + 3)).card : ENNReal) * ENNReal.ofReal (1 / L)
      have hcount : (∑ q ∈ stabIndex (k + 3),
          Set.indicator (badSet q)
            (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x)
          = (((stabIndex (k + 3)).filter fun q => x ∈ badSet q).card : ENNReal) := by
        rw [Finset.sum_congr rfl (fun q _ => by
          rw [Set.indicator_apply] : ∀ q ∈ stabIndex (k + 3),
            Set.indicator (badSet q)
              (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x
              = if x ∈ badSet q then (1 : ENNReal) else 0)]
        rw [Finset.sum_boole]
      rw [hcount]
      by_cases hxs : x ∈ simpleLocus hPP
      · have hfilter : ((stabIndex (k + 3)).filter fun q => x ∈ badSet q)
            = ((lagrBases (k + 3)) ×ˢ (Finset.univ : Finset (Fin (k + 3) → ZMod 2))).filter
              fun q => 2 * L < ((2 : ℝ) ^ (k + 3) + 1) *
                ∑ j, (finitePureStateFidelity
                  (registerEigenBasis (k + 3) hPP x j) (χ q.1 q.2)) ^ 2 := by
          rw [stabIndex]
          refine Finset.filter_congr fun q _ => ?_
          rw [hbadDef]
          have hcc : crossCollision hPP (stabSeed (k + 3) χ q) x
              = ∑ j, (finitePureStateFidelity
                  (registerEigenBasis (k + 3) hPP x j) (χ q.1 q.2)) ^ 2 := by
            rw [hPPdef]
            exact crossCollision_stabSeed k χ q (by rw [hPPdef] at hxs; exact hxs)
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (k + 3) + 1 := by positivity
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, hxs, true_and, hcc,
            hc₀def]
          rw [div_lt_iff₀ hpos]
          constructor
          · intro h; nlinarith [h]
          · intro h; nlinarith [h]
        rw [hfilter]
        have hdes := hdesign (registerEigenBasis (k + 3) hPP x)
          (sum_normSq_registerEigenBasis (k + 3) hPP x)
        have hmark := card_filter_collision_gt_mul_le (registerEigenBasis (k + 3) hPP x) χ hdes L
        have hcardT : ((stabIndex (k + 3)).card : ℝ)
            = ((lagrBases (k + 3)).card : ℝ) * 2 ^ (k + 3) := by
          rw [card_stabIndex]
          push_cast
          ring
        have hle : ((((lagrBases (k + 3)) ×ˢ
              (Finset.univ : Finset (Fin (k + 3) → ZMod 2))).filter fun q =>
              2 * L < ((2 : ℝ) ^ (k + 3) + 1) *
                ∑ j, (finitePureStateFidelity
                  (registerEigenBasis (k + 3) hPP x j) (χ q.1 q.2)) ^ 2).card : ℝ)
            ≤ ((stabIndex (k + 3)).card : ℝ) * (1 / L) := by
          rw [hcardT, mul_one_div, le_div_iff₀ hL]
          exact hmark
        have hE := ENNReal.ofReal_le_ofReal hle
        rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast] at hE
        exact hE
      · have hempty : ((stabIndex (k + 3)).filter fun q => x ∈ badSet q) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun q _ => ?_
          rw [hbadDef]
          intro hcon
          exact hxs hcon.1
        rw [hempty]
        simp
    · rw [lintegral_const, measure_univ, mul_one]
  · intro q _
    exact (measurable_const.indicator (hbadmeas q))
end

end GaloisForLFunctions.HTGeometry
