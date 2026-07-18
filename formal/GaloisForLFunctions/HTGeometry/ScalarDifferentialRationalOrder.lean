import GaloisForLFunctions.HTGeometry.SimpleTranscendentalIntersection
import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingCovariance

/-!
# Intrinsic order in a scalar differential rational field

The differential order of a nonconstant element of `C⟨y⟩` is encoded intrinsically by the
finite jet-observable filtration.  This file proves exact order under differentiation and
differential substitution, and extracts the classical no-DA-shadow bridge: every nonconstant
element of the free scalar differential rational field is hypertranscendental.

The no-DA-shadow theorem is classical differential algebra and is used here only as formal
infrastructure; no novelty claim is attached to it.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A nonconstant scalar differential rational observable has exact order `n` when it first
appears after adjoining the `n`-th jet. -/
def HasScalarDifferentialOrder
    (C : Type*) {E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (y z : E) (n : ℕ) : Prop :=
  z ∈ jetObservableField C y (n + 1) ∧ z ∉ jetObservableField C y n

/-- The order-zero observable field is just the embedded coefficient field. -/
@[simp] theorem jetObservableField_zero
    (C : Type*) {E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (y : E) :
    jetObservableField C y 0 = ⊥ := by
  simp [jetObservableField]

set_option maxHeartbeats 800000 in
theorem exists_jetObservableField_of_mem_differentialAdjoin
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {y z : E} (hz : z ∈ differentialAdjoin C ({y} : Set E)) :
    ∃ N : ℕ, z ∈ jetObservableField C y N := by
  rw [differentialAdjoin] at hz
  obtain ⟨T, hT, hzT⟩ := IntermediateField.exists_finset_of_mem_adjoin hz
  classical
  have hwitness : ∀ w : {w // w ∈ T}, ∃ n : ℕ, differentialJet n y = w.1 := by
    intro w
    obtain ⟨x, hx, n, hn⟩ := hT w.2
    exact ⟨n, by simpa only [Set.mem_singleton_iff.mp hx] using hn⟩
  choose order horder using hwitness
  let orders : Finset ℕ := Finset.univ.image order
  let N : ℕ := orders.sup id + 1
  refine ⟨N, ?_⟩
  have hle : IntermediateField.adjoin C (T : Set E) ≤ jetObservableField C y N := by
    apply IntermediateField.adjoin.mono C
    intro w hwT
    let wt : {w // w ∈ T} := ⟨w, hwT⟩
    refine ⟨order wt, ?_, horder wt⟩
    have hnOrders : order wt ∈ orders := by
      exact Finset.mem_image.mpr ⟨wt, Finset.mem_univ wt, rfl⟩
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hnOrders) (Nat.lt_succ_self _)
  exact hle hzT

set_option maxHeartbeats 800000 in
theorem existsUnique_hasScalarDifferentialOrder
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {y z : E} (hz : z ∈ differentialAdjoin C ({y} : Set E))
    (hzC : z ∉ (⊥ : IntermediateField C E)) :
    ∃! n : ℕ, HasScalarDifferentialOrder C y z n := by
  classical
  obtain ⟨N, hN⟩ := exists_jetObservableField_of_mem_differentialAdjoin hz
  have hexists : ∃ N : ℕ, z ∈ jetObservableField C y N := ⟨N, hN⟩
  let first : ℕ := Nat.find hexists
  have hfirst : z ∈ jetObservableField C y first := Nat.find_spec hexists
  have hfirstPos : 0 < first := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hzC
    simpa [hzero] using hfirst
  obtain ⟨n, hfirstEq⟩ := Nat.exists_eq_succ_of_ne_zero hfirstPos.ne'
  have hmemSucc : z ∈ jetObservableField C y (n + 1) := by
    simpa [hfirstEq] using hfirst
  have hnot : z ∉ jetObservableField C y n := by
    intro hn
    have hmin := Nat.find_min' hexists hn
    dsimp only [first] at hfirstEq
    omega
  refine ⟨n, ⟨hmemSucc, hnot⟩, ?_⟩
  · intro m hm
    rcases lt_trichotomy m n with hmn | rfl | hnm
    · exfalso
      exact hnot (jetObservableField_mono y (Nat.succ_le_iff.mpr hmn) hm.1)
    · rfl
    · exfalso
      exact hm.2 (jetObservableField_mono y (Nat.succ_le_iff.mpr hnm) hmemSucc)

/-- Exact scalar differential order is unique whenever it is defined. -/
theorem HasScalarDifferentialOrder.order_eq
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {y z : E} {m n : ℕ}
    (hm : HasScalarDifferentialOrder C y z m)
    (hn : HasScalarDifferentialOrder C y z n) : m = n := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exfalso
    exact hn.2 (jetObservableField_mono y (Nat.succ_le_iff.mpr hmn) hm.1)
  · exact hmn
  · exfalso
    exact hm.2 (jetObservableField_mono y (Nat.succ_le_iff.mpr hnm) hn.1)

/-- Exact order zero means a nonconstant ordinary rational function of the source value. -/
theorem hasScalarDifferentialOrder_zero_iff
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {y z : E} :
    HasScalarDifferentialOrder C y z 0 ↔
      z ∈ IntermediateField.adjoin C ({y} : Set E) ∧
        z ∉ (⊥ : IntermediateField C E) := by
  simp [HasScalarDifferentialOrder, jetObservableField]

/-- Successive transcendence over all preceding values implies algebraic independence of a
sequence. -/
theorem algebraicIndependent_nat_of_transcendental_prefix
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (j : ℕ → E)
    (h : ∀ n : ℕ, Transcendental
      (IntermediateField.adjoin C (j '' Set.Iio n)) (j n)) :
    AlgebraicIndependent C j := by
  have hprefix : ∀ n : ℕ, AlgebraicIndepOn C j (Set.Iio n) := by
    intro n
    induction n with
    | zero => simpa using (algebraicIndependent_empty_type :
        AlgebraicIndependent C (fun i : (∅ : Set ℕ) => j i))
    | succ n ih =>
        rw [show Set.Iio (n + 1) = insert n (Set.Iio n) by ext m; simp]
        exact ih.insert (IntermediateField.transcendental_adjoin_iff.mp (h n))
  have hjinj : Function.Injective j := by
    intro m n hmn
    let N := max m n + 1
    have hm : m ∈ Set.Iio N := by simp [N]
    have hn : n ∈ Set.Iio N := by simp [N]
    have hinj := (hprefix N).injective
    exact congrArg Subtype.val
      (hinj (a₁ := ⟨m, hm⟩) (a₂ := ⟨n, hn⟩) hmn)
  have hsets : (⋃ n : ℕ, j '' Set.Iio n) = Set.range j := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨n, m, -, rfl⟩ := hz
      exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩
      rw [Set.mem_iUnion]
      exact ⟨m + 1, m, Nat.lt_succ_self m, rfl⟩
  have hunion : AlgebraicIndependent C
      (fun z : (⋃ n : ℕ, j '' Set.Iio n) => (z : E)) := by
    apply algebraicIndependent_iUnion_of_directed
    · have hmono : Monotone (fun n : ℕ => j '' Set.Iio n) :=
        fun _ _ hmn => Set.image_mono (Set.Iio_subset_Iio hmn)
      exact hmono.directed_le
    · exact fun n => (hprefix n).image
  rw [hsets] at hunion
  exact (algebraicIndependent_subtype_range hjinj).mp hunion

/-- An exact-order observable is transcendental over the preceding jet-observable field. -/
theorem HasScalarDifferentialOrder.transcendental
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {y z : E} {n : ℕ} (hy : HypertranscendentalOver C y)
    (hz : HasScalarDifferentialOrder C y z n) :
    Transcendental (jetObservableField C y n) z := by
  let P : IntermediateField C E := jetObservableField C y n
  let t : E := differentialJet n y
  let Q : IntermediateField P E := IntermediateField.adjoin P {t}
  have hstep : jetObservableField C y (n + 1) = Q.restrictScalars C :=
    jetObservableField_succ C y n
  have hzQ : z ∈ Q := by
    change z ∈ Q.restrictScalars C
    rw [← hstep]
    exact hz.1
  have hzP : z ∉ P := hz.2
  have ht : Transcendental P t :=
    hypertranscendental_jet_transcendental_observableField hy n
  let e : RatFunc P ≃ₐ[P] Q := RatFunc.algEquivOfTranscendental t ht
  let zQ : Q := ⟨z, hzQ⟩
  let w : RatFunc P := e.symm zQ
  have hwne : ¬ ∃ c : P, w = RatFunc.C c := by
    rintro ⟨c, hc⟩
    apply hzP
    have hew : e w = zQ := e.apply_symm_apply zQ
    rw [hc, ← RatFunc.algebraMap_eq_C, e.commutes] at hew
    have hval := congrArg Subtype.val hew
    change (c : E) = z at hval
    rw [← hval]
    exact c.2
  have hwt : Transcendental P w := w.transcendental_of_ne_C hwne
  intro hzalg
  have hzQalg : IsAlgebraic P zQ :=
    (isAlgebraic_algHom_iff Q.val Subtype.val_injective).mp hzalg
  apply hwt
  apply (isAlgebraic_algHom_iff e.toAlgHom e.injective).mp
  simpa [w] using hzQalg

/-- Applying `r` derivatives raises exact scalar differential order by exactly `r`. -/
theorem HasScalarDifferentialOrder.differentialJet_order
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y z : E} {n : ℕ} (hy : HypertranscendentalOver C y)
    (hz : HasScalarDifferentialOrder C y z n) (r : ℕ) :
    HasScalarDifferentialOrder C y (differentialJet r z) (n + r) := by
  constructor
  · have hmem := differentialJet_mem_jetObservableField_add y hz.1 r
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  · intro hlow
    have hall : ∀ q : ℕ, q ≤ r →
        differentialJet q z ∈ jetObservableField C y (n + r) := by
      intro q hqr
      rcases lt_or_eq_of_le hqr with hlt | rfl
      · have hmem := differentialJet_mem_jetObservableField_add y hz.1 q
        exact jetObservableField_mono y (by omega) hmem
      · exact hlow
    exact hz.2 ((hypertranscendental_clock_erosion_iff hy n r).mp hall)

/-- A source of exact order `r` exposes its first `N` jets within source resolution `r+N`. -/
theorem jetObservableField_le_of_hasScalarDifferentialOrder
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y v : E} {r : ℕ} (hy : HypertranscendentalOver C y)
    (hv : HasScalarDifferentialOrder C y v r) (N : ℕ) :
    jetObservableField C v N ≤ jetObservableField C y (r + N) := by
  rw [jetObservableField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, hi, rfl⟩
  change i < N at hi
  have hiOrder := hv.differentialJet_order hy i
  exact jetObservableField_mono y (by omega) hiOrder.1

/-- Exact scalar differential orders add under differential-rational composition. -/
theorem HasScalarDifferentialOrder.comp
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y v z : E} {r m : ℕ} (hy : HypertranscendentalOver C y)
    (hv : HasScalarDifferentialOrder C y v r)
    (hz : HasScalarDifferentialOrder C v z m) :
    HasScalarDifferentialOrder C y z (m + r) := by
  constructor
  · have hmem :=
      (jetObservableField_le_of_hasScalarDifferentialOrder hy hv (m + 1)) hz.1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  · intro hlow
    let K : IntermediateField C E := jetObservableField C v m
    let L : IntermediateField C E := jetObservableField C y (r + m)
    let t : E := differentialJet m v
    have hKL : K ≤ L := by
      simpa [K, L] using
        (jetObservableField_le_of_hasScalarDifferentialOrder hy hv m)
    have htOrder : HasScalarDifferentialOrder C y t (r + m) :=
      hv.differentialJet_order hy m
    have ht : Transcendental L t := by
      exact htOrder.transcendental hy
    have hzKt : z ∈ IntermediateField.adjoin K {t} := by
      change z ∈ (IntermediateField.adjoin K {t}).restrictScalars C
      rw [← jetObservableField_succ C v m]
      exact hz.1
    have hzL : z ∈ L := by
      simpa [L, Nat.add_comm] using hlow
    have hzK : z ∈ K :=
      mem_left_of_mem_adjoin_simple_of_mem_of_transcendental K L hKL ht hzKt hzL
    exact hz.2 hzK

/-- A derivation-preserving field embedding preserves exact scalar differential order. -/
theorem HasScalarDifferentialOrder.map
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {y z : E} {n : ℕ} (e : E →ₐ[C] E)
    (hderiv : ∀ w : E, e w′ = (e w)′)
    (hz : HasScalarDifferentialOrder C y z n) :
    HasScalarDifferentialOrder C (e y) (e z) n := by
  constructor
  · rw [← jetObservableField_map_algHom e hderiv y (n + 1)]
    exact (IntermediateField.map_mem_map
      (S := jetObservableField C y (n + 1)) e (x := z)).mpr hz.1
  · intro hlow
    apply hz.2
    rw [← jetObservableField_map_algHom e hderiv y n] at hlow
    exact (IntermediateField.map_mem_map
      (S := jetObservableField C y n) e (x := z)).mp hlow

/-- Substitution by an exact-order differential embedding adds its source order. -/
theorem HasScalarDifferentialOrder.algHom
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y z : E} {m r : ℕ} (e : E →ₐ[C] E)
    (hderiv : ∀ w : E, e w′ = (e w)′)
    (hy : HypertranscendentalOver C y)
    (hz : HasScalarDifferentialOrder C y z m)
    (hey : HasScalarDifferentialOrder C y (e y) r) :
    HasScalarDifferentialOrder C y (e z) (m + r) :=
  HasScalarDifferentialOrder.comp hy hey (hz.map e hderiv)

/-- Every nonconstant finite-order observable of a free scalar differential field remains
hypertranscendental over the coefficient field. -/
theorem HasScalarDifferentialOrder.hypertranscendentalOver
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y z : E} {n : ℕ} (hy : HypertranscendentalOver C y)
    (hz : HasScalarDifferentialOrder C y z n) :
    HypertranscendentalOver C z := by
  have hj : AlgebraicIndependent C (fun q : ℕ ↦ differentialJet q z) :=
    algebraicIndependent_nat_of_transcendental_prefix
      (fun q : ℕ ↦ differentialJet q z) (by
        intro q
        change Transcendental (jetObservableField C z q) (differentialJet q z)
        exact Transcendental.of_tower_top_of_subalgebra_le
          (jetObservableField_le_of_hasScalarDifferentialOrder hy hz q)
          ((hz.differentialJet_order hy q).transcendental hy))
  apply (hypertranscendentalOver_iff_differentialIndependent_singleton C z).mpr
  unfold DifferentialIndependent
  have h := hj.comp (fun p : Unit × ℕ ↦ p.2) (by
    rintro ⟨u, m⟩ ⟨v, q⟩ hmq
    cases u
    cases v
    exact Prod.ext rfl hmq)
  exact h

/-- **No differential-algebraic shadow.**  A nonconstant member of the scalar free differential
field generated by a hypertranscendental source is itself hypertranscendental. -/
theorem differentialRational_noDAShadow
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y z : E} (hy : HypertranscendentalOver C y)
    (hz : z ∈ differentialAdjoin C ({y} : Set E))
    (hzC : z ∉ (⊥ : IntermediateField C E)) :
    HypertranscendentalOver C z := by
  obtain ⟨n, hn, -⟩ := existsUnique_hasScalarDifferentialOrder hz hzC
  exact hn.hypertranscendentalOver hy

/-- Exact order grows arithmetically under iterated differential substitution. -/
theorem HasScalarDifferentialOrder.algHom_pow
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    {y z : E} {m r : ℕ} (e : E →ₐ[C] E)
    (hderiv : ∀ w : E, e w′ = (e w)′)
    (hy : HypertranscendentalOver C y)
    (hey : HasScalarDifferentialOrder C y (e y) r)
    (hz : HasScalarDifferentialOrder C y z m) (q : ℕ) :
    HasScalarDifferentialOrder C y ((e ^ q) z) (m + q * r) := by
  induction q with
  | zero => simpa only [pow_zero, AlgHom.one_apply, Nat.zero_mul, Nat.add_zero] using hz
  | succ q ih =>
      have hnext := HasScalarDifferentialOrder.algHom e hderiv hy ih hey
      have hvalue : (e ^ (q + 1)) z = e ((e ^ q) z) := by
        simp only [AlgHom.coe_pow, Function.iterate_succ_apply']
      have horder : m + (q + 1) * r = (m + q * r) + r := by
        simp [Nat.add_mul, Nat.add_assoc]
      rw [hvalue, horder]
      exact hnext

/-- A differential automorphism of a scalar free differential field sends its generator, and the
inverse sends the generator, by exact order-zero differential rational functions. -/
theorem differentialAlgEquiv_generator_order_zero
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′) :
    HasScalarDifferentialOrder C y (σ y) 0 ∧
      HasScalarDifferentialOrder C y (σ.symm y) 0 := by
  have hty : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  have hyC : y ∉ (⊥ : IntermediateField C E) := by
    intro hybot
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hybot
    exact hty (hc ▸ isAlgebraic_algebraMap c)
  have hσC : σ y ∉ (⊥ : IntermediateField C E) := by
    intro hσbot
    apply hyC
    rw [IntermediateField.mem_bot]
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hσbot
    refine ⟨c, ?_⟩
    calc
      algebraMap C E c = σ.symm (algebraMap C E c) := (σ.symm.commutes c).symm
      _ = σ.symm (σ y) := congrArg σ.symm hc
      _ = y := σ.symm_apply_apply y
  have hσinvC : σ.symm y ∉ (⊥ : IntermediateField C E) := by
    intro hσinvbot
    apply hyC
    rw [IntermediateField.mem_bot]
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hσinvbot
    refine ⟨c, ?_⟩
    calc
      algebraMap C E c = σ (algebraMap C E c) := (σ.commutes c).symm
      _ = σ (σ.symm y) := congrArg σ hc
      _ = y := σ.apply_symm_apply y
  have hσmem : σ y ∈ differentialAdjoin C ({y} : Set E) := by
    rw [hytop]
    trivial
  have hσinvmem : σ.symm y ∈ differentialAdjoin C ({y} : Set E) := by
    rw [hytop]
    trivial
  obtain ⟨r, hr, -⟩ := existsUnique_hasScalarDifferentialOrder hσmem hσC
  obtain ⟨m, hm, -⟩ := existsUnique_hasScalarDifferentialOrder hσinvmem hσinvC
  have hmapped : HasScalarDifferentialOrder C (σ y) y m := by
    simpa using hm.map σ.toAlgHom hderiv
  have hsum : HasScalarDifferentialOrder C y y (m + r) :=
    HasScalarDifferentialOrder.comp hy hr hmapped
  have hyzero : HasScalarDifferentialOrder C y y 0 := by
    rw [hasScalarDifferentialOrder_zero_iff]
    exact ⟨IntermediateField.subset_adjoin C ({y} : Set E) (Set.mem_singleton y), hyC⟩
  have hmr : m + r = 0 := hsum.order_eq hyzero
  have hm0 : m = 0 := by omega
  have hr0 : r = 0 := by omega
  exact ⟨hr0 ▸ hr, hm0 ▸ hm⟩

/-- Membership form of `differentialAlgEquiv_generator_order_zero`: every differential
automorphism of a scalar free differential field preserves its ordinary generator field in both
directions. -/
theorem differentialAlgEquiv_generator_mem_adjoin_singleton
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′) :
    σ y ∈ IntermediateField.adjoin C ({y} : Set E) ∧
      σ.symm y ∈ IntermediateField.adjoin C ({y} : Set E) := by
  have hzero := differentialAlgEquiv_generator_order_zero σ hy hytop hderiv
  exact ⟨(hasScalarDifferentialOrder_zero_iff.mp hzero.1).1,
    (hasScalarDifferentialOrder_zero_iff.mp hzero.2).1⟩

end

end GaloisForLFunctions.HTGeometry
