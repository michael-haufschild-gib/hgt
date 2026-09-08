import GaloisForLFunctions.HTGeometry.BlockSplitBranchEscape
import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint
import GaloisForLFunctions.HTGeometry.TwoLocalFullStarSpectrum
import GaloisForLFunctions.HTGeometry.HypercubeCharacterNonconstancy
import GaloisForLFunctions.HTGeometry.EdgeBlockReindex
import GaloisForLFunctions.HTGeometry.BaseThreeSignSeparation

/-!
# A finite-order spectral certificate from ordinary two-local star slices

At the single diagonal reference field `h i = 3^i / 3^n`, every balanced nonzero integer
spectral character has a literal mixed parameter derivative of total order at most `n+1`
and magnitude at least one. The reference field is independent of the character and replica
order; its spectrum is simple. Every selected-spin branch starts at that same labelled base.

The producer is explicit. Two transverse derivatives yield a reciprocal affine gap. Further
squarefree derivatives in distinguished-spin pair couplings yield a factorial times a Walsh
coefficient. The corpus's Walsh inversion then detects every nonzero edge packet. The exact
blind kernel for one selected spin consists of characters equal across each of its edges.

The matrix realization and characteristic-root identities identify genuine real-coefficient,
time-independent two-local star slices, rather than assigning an arbitrary spectral jet.

Scope: this is a local source certificate. It gives no typical-draw estimate, quantitative
common neighbourhood, global analytic-chart transfer, occupied-image bound, fibre-sheet bound,
post-ramp time cutoff, or complete-circuit exclusion estimate. In particular it does not prove
the growing-replica return-excised incidence-action inequality.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance starResponseCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

/-- Ordered literal coordinate derivatives in the real coupling parameters. -/
def orderedStarCouplingDeriv {I : Type*} [DecidableEq I]
    (sites : List I) (f : (I → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  match sites with
  | [] => f
  | i :: rest => fun c =>
      deriv (fun t => orderedStarCouplingDeriv rest f (Function.update c i t)) (c i)

/-- Half of the two-level splitting seen by a distinguished spin in a Boolean environment.
Each coupling multiplies one spectator sign, so its Hamiltonian interaction is two-local. -/
def twoLocalStarGap {I : Type*} [Fintype I]
    (a : ℝ) (c : I → ℝ) (z : I → Bool) : ℝ :=
  a + ∑ j, c j * (if z j then -1 else 1)

/-- The physical transverse curvature, written as its reciprocal-gap expression. -/
def twoLocalStarCurvature {I : Type*} [Fintype I]
    (a : ℝ) (β : (I → Bool) → ℝ) (c : I → ℝ) : ℝ :=
  ∑ z, β z * (twoLocalStarGap a c z)⁻¹

private theorem hasDerivAt_twoLocalStarGap_update
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (c : I → ℝ) (z : I → Bool) (i : I) :
    HasDerivAt (fun t => twoLocalStarGap a (Function.update c i t) z)
      (if z i then -1 else 1) (c i) := by
  have hs : HasDerivAt
      (fun t => ∑ j, Function.update c i t j * (if z j then -1 else 1))
      (∑ j, if j = i then (if z j then (-1 : ℝ) else 1) else 0) (c i) := by
    apply HasDerivAt.fun_sum
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using (hasDerivAt_id (c i)).mul_const (if z i then (-1 : ℝ) else 1)
    · simpa [Function.update_of_ne hji, hji] using
        hasDerivAt_const (c i) (c j * (if z j then (-1 : ℝ) else 1))
  simpa [twoLocalStarGap] using hs.const_add a

private theorem continuous_twoLocalStarGap
    {I : Type*} [Fintype I] (a : ℝ) (z : I → Bool) :
    Continuous (fun c : I → ℝ => twoLocalStarGap a c z) := by
  unfold twoLocalStarGap
  fun_prop

/-- The reciprocal response has an exact mixed derivative in every ordered coupling direction.
Repeated coordinates are allowed; no nonflatness or lower-bound assumption occurs. -/
theorem orderedStarCouplingDeriv_curvature
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (β : (I → Bool) → ℝ) (sites : List I)
    (c : I → ℝ) (hc : ∀ z, twoLocalStarGap a c z ≠ 0) :
    orderedStarCouplingDeriv sites (twoLocalStarCurvature a β) c =
      (-1 : ℝ) ^ sites.length * (sites.length.factorial : ℝ) *
        ∑ z, β z * (sites.map (fun j => if z j then (-1 : ℝ) else 1)).prod *
          ((twoLocalStarGap a c z)⁻¹) ^ (sites.length + 1) := by
  induction sites generalizing c with
  | nil => simp [orderedStarCouplingDeriv, twoLocalStarCurvature]
  | cons i sites ih =>
    let C : ℝ := (-1 : ℝ) ^ sites.length * (sites.length.factorial : ℝ)
    let P : (I → Bool) → ℝ :=
      fun z => (sites.map (fun j => if z j then (-1 : ℝ) else 1)).prod
    have hnear : ∀ᶠ t in 𝓝 (c i),
        ∀ z, twoLocalStarGap a (Function.update c i t) z ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro z
      have hcont := (hasDerivAt_twoLocalStarGap_update a c z i).continuousAt
      exact hcont.eventually_ne (by simpa using hc z)
    have heq :
        (fun t => orderedStarCouplingDeriv sites (twoLocalStarCurvature a β)
          (Function.update c i t)) =ᶠ[𝓝 (c i)]
        (fun t => C * ∑ z, β z * P z *
          ((twoLocalStarGap a (Function.update c i t) z)⁻¹) ^ (sites.length + 1)) := by
      filter_upwards [hnear] with t ht
      exact ih _ ht
    have hterm : ∀ z, HasDerivAt
        (fun t => β z * P z *
          ((twoLocalStarGap a (Function.update c i t) z)⁻¹) ^ (sites.length + 1))
        (-(sites.length + 1 : ℕ) * (β z * P z) *
          (if z i then (-1 : ℝ) else 1) *
          ((twoLocalStarGap a c z)⁻¹) ^ (sites.length + 2)) (c i) := by
      intro z
      have hg := hasDerivAt_twoLocalStarGap_update a c z i
      have ht := ((hg.fun_inv (by simpa using hc z)).fun_pow
        (sites.length + 1)).const_mul (β z * P z)
      convert! ht using 1
      simp only [Function.update_eq_self, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        pow_succ]
      field_simp
    unfold orderedStarCouplingDeriv
    rw [heq.deriv_eq, ((HasDerivAt.fun_sum (fun z _ => hterm z)).const_mul C).deriv]
    simp only [List.length_cons, List.map_cons, List.prod_cons, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [P]
    ring

theorem orderedStarCouplingDeriv_curvature_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : a ≠ 0) (β : (I → Bool) → ℝ) (S : Finset I) :
    orderedStarCouplingDeriv S.toList (twoLocalStarCurvature a β) 0 =
      (-1 : ℝ) ^ S.card * (S.card.factorial : ℝ) * (a⁻¹) ^ (S.card + 1) *
        ∑ z, β z * ∏ j ∈ S, (if z j then (-1 : ℝ) else 1) := by
  rw [orderedStarCouplingDeriv_curvature a β S.toList 0
    (by intro z; simpa [twoLocalStarGap] using ha)]
  simp only [Finset.length_toList, Finset.prod_map_toList, twoLocalStarGap,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_mul]
  ring

/-- Germ locality of ordered derivatives; no differentiability premise is needed. -/
theorem orderedStarCouplingDeriv_congr
    {I : Type*} [Fintype I] [DecidableEq I]
    (sites : List I) {f g : (I → ℝ) → ℝ} {c : I → ℝ}
    (h : f =ᶠ[𝓝 c] g) :
    orderedStarCouplingDeriv sites f c = orderedStarCouplingDeriv sites g c := by
  induction sites generalizing c with
  | nil => exact h.eq_of_nhds
  | cons i sites ih =>
    apply Filter.EventuallyEq.deriv_eq
    have ht : Tendsto (fun t : ℝ => Function.update c i t) (𝓝 (c i)) (𝓝 c) := by
      have hcont : Continuous (fun t : ℝ => Function.update c i t) := by fun_prop
      simpa using hcont.tendsto (c i)
    filter_upwards [ht.eventually h.eventuallyEq_nhds] with t ht
    exact ih ht

/-- The mixed derivatives above are derivatives of literal spectral curvature, not an assigned jet.
The underlying square roots are the characteristic roots of `blockSplitMatrix`. -/
theorem orderedStarCouplingDeriv_actualSpectralCurvature
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (β : (I → Bool) → ℝ) (constant : ℝ) (S : Finset I) :
    orderedStarCouplingDeriv S.toList
        (fun c => deriv (deriv
          (blockSplitRelation constant β (twoLocalStarGap a c))) 0) 0 =
      (-1 : ℝ) ^ S.card * (S.card.factorial : ℝ) * (a⁻¹) ^ (S.card + 1) *
        ∑ z, β z * ∏ j ∈ S, (if z j then (-1 : ℝ) else 1) := by
  have hpos : ∀ᶠ c in 𝓝 (0 : I → ℝ), ∀ z, 0 < twoLocalStarGap a c z := by
    apply Filter.eventually_all.mpr
    intro z
    exact ((continuous_twoLocalStarGap a z).continuousAt).eventually
      (Ioi_mem_nhds (by simpa [twoLocalStarGap] using ha))
  have heq : (fun c => deriv (deriv
      (blockSplitRelation constant β (twoLocalStarGap a c))) 0) =ᶠ[𝓝 0]
      twoLocalStarCurvature a β := by
    filter_upwards [hpos] with c hc
    rw [(hasDerivAt_deriv_blockSplitRelation_zero constant β (twoLocalStarGap a c)
      (fun z => ne_of_gt (hc z))).deriv]
    simp only [twoLocalStarCurvature]
    apply Finset.sum_congr rfl
    intro z hz
    rw [abs_of_pos (hc z), one_div]
  rw [orderedStarCouplingDeriv_congr S.toList heq]
  exact orderedStarCouplingDeriv_curvature_zero a (ne_of_gt ha) β S

/-- Integer Walsh packet. It is not normalized by the exponentially large Hilbert dimension. -/
def integerStarWalshPacket {I : Type*} [Fintype I]
    (β : (I → Bool) → ℤ) (S : Finset I) : ℤ :=
  ∑ z, β z * ∏ j ∈ S, (if z j then (-1 : ℤ) else 1)

theorem integerStarWalshPacket_cast_real
    {I : Type*} [Fintype I] (β : (I → Bool) → ℤ) (S : Finset I) :
    (integerStarWalshPacket β S : ℝ) =
      ∑ z, (β z : ℝ) * ∏ j ∈ S, (if z j then (-1 : ℝ) else 1) := by
  simp [integerStarWalshPacket]

/-- Walsh inversion prevents a nonzero integer packet from hiding in all mixed responses. -/
theorem exists_integerStarWalshPacket_ne_zero
    {I : Type*} [Fintype I] (β : (I → Bool) → ℤ) (hβ : β ≠ 0) :
    ∃ S : Finset I, integerStarWalshPacket β S ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hcoeff : ∀ S : Finset I,
      inverseWalshCoefficient (fun z => (β z : ℂ)) S = 0 := by
    intro S
    have hc := congrArg (fun b : ℤ => (b : ℂ)) (h S)
    simp only [integerStarWalshPacket] at hc
    push_cast at hc
    simp [inverseWalshCoefficient, orientationWalshCharacter, primeDirichletSign, hc]
  apply hβ
  funext z
  have hz := orientationWalsh_inversion (fun x => (β x : ℂ)) z
  simp only [hcoeff, zero_mul, Finset.sum_const_zero] at hz
  exact_mod_cast hz.symm

/-- Explicit quantitative source detection. Some derivative of order at most `card I + 2`
(two transverse derivatives plus a squarefree coupling derivative) has magnitude at least
`|S|! / a^(|S|+1)`. The bound is independent of integer packet size and hence replica count. -/
theorem exists_twoLocalStar_integerSpectralCurvature_detection
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (β : (I → Bool) → ℤ) (hβ : β ≠ 0)
    (constant : ℝ) :
    ∃ S : Finset I, S.card + 2 ≤ Fintype.card I + 2 ∧
      (S.card.factorial : ℝ) * (a⁻¹) ^ (S.card + 1) ≤
        |orderedStarCouplingDeriv S.toList
          (fun c => deriv (deriv
            (blockSplitRelation constant (fun z => (β z : ℝ))
              (twoLocalStarGap a c))) 0) 0| := by
  obtain ⟨S, hS⟩ := exists_integerStarWalshPacket_ne_zero β hβ
  refine ⟨S, Nat.add_le_add_right (Finset.card_le_univ S) 2, ?_⟩
  rw [orderedStarCouplingDeriv_actualSpectralCurvature a ha]
  rw [← integerStarWalshPacket_cast_real]
  have hb : (1 : ℝ) ≤ |(integerStarWalshPacket β S : ℝ)| := by
    exact_mod_cast Int.one_le_abs hS
  have hf : 0 ≤ (S.card.factorial : ℝ) := by positivity
  have hp : 0 ≤ (a⁻¹) ^ (S.card + 1) := by positivity
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hf, abs_of_nonneg hp]
  nlinarith [mul_nonneg hf hp]

/-- Ordinary distinguished-star Hamiltonian, expressed by its exact two-level blocks. -/
def twoLocalResponseStarMatrix {m : ℕ}
    (a : ℝ) (onsite coupling : Fin m → ℝ) (u : ℝ) :
    Matrix (Bool × (Fin m → Bool)) (Bool × (Fin m → Bool)) ℂ :=
  Matrix.reindex (twoLocalFullIndexEquiv m) (twoLocalFullIndexEquiv m)
    (blockSplitMatrix
      (fun z => ∑ j, onsite j * (if z j then -1 else 1))
      (twoLocalStarGap a coupling) (u : ℂ))

/-- Coefficient-by-coefficient realization with onsite, pair, and one transverse term.
Thus the derivative producer is an ordinary two-local Hamiltonian slice. -/
theorem twoLocalResponseStarMatrix_eq_distinguishedStar {m : ℕ}
    (a : ℝ) (onsite coupling : Fin m → ℝ) (u : ℝ) :
    twoLocalResponseStarMatrix a onsite coupling u =
      distinguishedStarTwoLocalHamiltonian
        ((a + ∑ j, onsite j + ∑ j, coupling j : ℝ) : ℂ)
        ((-2 * (a + ∑ j, coupling j) : ℝ) : ℂ) (u : ℂ)
        (fun j => ((-2 * (onsite j + coupling j) : ℝ) : ℂ))
        (fun j => ((4 * coupling j : ℝ) : ℂ)) := by
  ext ⟨b, z⟩ ⟨d, y⟩
  have hindex (b : Bool) (z : Fin m → Bool) :
      (twoLocalFullIndexEquiv m).symm (b, z) =
        ((if b then 1 else 0), z) := by cases b <;> rfl
  simp only [twoLocalResponseStarMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, hindex]
  by_cases hzy : z = y
  · subst y
    cases b <;> cases d <;>
      simp [blockSplitMatrix, Matrix.blockDiagonal_apply_eq,
        distinguishedStarTwoLocalHamiltonian, splitBlock, boolOccupation]
    all_goals
      simp only [twoLocalStarGap]
      have hlin (w : ℝ) (b : Bool) : (if b then -w else w) =
          w * (1 - 2 * (boolOccupation b : ℝ)) := by
        cases b <;> norm_num [boolOccupation]
      simp_rw [hlin]
      push_cast
      have hind (w : ℂ) (b : Bool) : (if b then w else 0) =
          w * (boolOccupation b : ℂ) := by
        cases b <;> simp [boolOccupation]
      simp_rw [hind]
      ring_nf
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      simp only [← Finset.sum_mul]
      ring
  · have hp : ∀ b d : Bool, (b, z) ≠ (d, y) := by
      intro b d h
      exact hzy (congrArg Prod.snd h)
    cases b <;> cases d <;>
      simp [blockSplitMatrix, Matrix.blockDiagonal_apply,
        distinguishedStarTwoLocalHamiltonian, hzy, hp]

theorem twoLocalResponseStarMatrix_isTwoLocal {m : ℕ}
    (a : ℝ) (onsite coupling : Fin m → ℝ) (u : ℝ) :
    IsComplexDistinguishedStarTwoLocalHamiltonian
      (twoLocalResponseStarMatrix a onsite coupling u) := by
  exact ⟨_, _, _, _, _, twoLocalResponseStarMatrix_eq_distinguishedStar a onsite coupling u⟩

theorem twoLocalResponseStarMatrix_isHermitian {m : ℕ}
    (a : ℝ) (onsite coupling : Fin m → ℝ) (u : ℝ) :
    (twoLocalResponseStarMatrix a onsite coupling u).IsHermitian := by
  unfold twoLocalResponseStarMatrix
  apply Matrix.IsHermitian.reindex
  apply Matrix.IsHermitian.ext
  rintro ⟨b, z⟩ ⟨d, y⟩
  by_cases hzy : z = y
  · subst y
    fin_cases b <;> fin_cases d <;>
      simp [blockSplitMatrix, Matrix.blockDiagonal_apply, splitBlock]
  · simp [blockSplitMatrix, Matrix.blockDiagonal_apply, hzy, Ne.symm hzy]

/-- Every labelled square-root branch belongs to this same full ordinary two-local matrix. -/
theorem twoLocalResponseStarMatrix_characteristicRoot {m : ℕ}
    (a : ℝ) (onsite coupling : Fin m → ℝ) (u : ℝ)
    (p : Fin 2 × (Fin m → Bool)) :
    (twoLocalResponseStarMatrix a onsite coupling u).charpoly.eval
      (blockSplitRoot (fun z => ∑ j, onsite j * (if z j then -1 else 1))
        (twoLocalStarGap a coupling) p u : ℂ) = 0 := by
  rw [twoLocalResponseStarMatrix, Matrix.charpoly_reindex, Matrix.eval_charpoly]
  exact matrixCharpolyRelation_blockSplitRoot _ _ p u

/-- The weighted action of all characteristic-root branches of one star matrix. -/
def twoLocalStarCharacterAction {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (mean : (I → Bool) → ℝ)
    (k : (Fin 2 × (I → Bool)) → ℤ) (c : I → ℝ) (u : ℝ) : ℝ :=
  ∑ p, (k p : ℝ) * blockSplitRoot mean (twoLocalStarGap a c) p u

theorem twoLocalStarCharacterAction_eq_relation
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (mean : (I → Bool) → ℝ)
    (k : (Fin 2 × (I → Bool)) → ℤ) (c : I → ℝ) :
    twoLocalStarCharacterAction a mean k c =
      blockSplitRelation (∑ z, ((k (0, z) : ℝ) + (k (1, z) : ℝ)) * mean z)
        (fun z => ((k (0, z) - k (1, z) : ℤ) : ℝ)) (twoLocalStarGap a c) := by
  funext u
  simpa [twoLocalStarCharacterAction] using
    sum_blockSplitRoot_eq mean (twoLocalStarGap a c) (fun p => (k p : ℝ)) u

/-- Exact mixed response for a full integer character, including both members of every block. -/
theorem orderedStarCouplingDeriv_characterAction
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (mean : (I → Bool) → ℝ)
    (k : (Fin 2 × (I → Bool)) → ℤ) (S : Finset I) :
    orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (twoLocalStarCharacterAction a mean k c)) 0) 0 =
      (-1 : ℝ) ^ S.card * (S.card.factorial : ℝ) * (a⁻¹) ^ (S.card + 1) *
        (integerStarWalshPacket (fun z => k (0, z) - k (1, z)) S : ℝ) := by
  simp_rw [twoLocalStarCharacterAction_eq_relation]
  rw [orderedStarCouplingDeriv_actualSpectralCurvature a ha,
    integerStarWalshPacket_cast_real]

/-- Exact kernel, not just existence of some response: squarefree coupling jets through order
`card I + 2` are blind precisely to characters equal across every distinguished-spin pair. -/
theorem twoLocalStarCharacterAction_allJets_zero_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (mean : (I → Bool) → ℝ)
    (k : (Fin 2 × (I → Bool)) → ℤ) :
    (∀ S : Finset I, orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (twoLocalStarCharacterAction a mean k c)) 0) 0 = 0) ↔
      ∀ z, k (0, z) = k (1, z) := by
  constructor
  · intro h
    by_contra hn
    have hβ : (fun z => k (0, z) - k (1, z)) ≠ 0 := by
      intro hzero
      apply hn
      intro z
      exact sub_eq_zero.mp (congrFun hzero z)
    obtain ⟨S, hS⟩ := exists_integerStarWalshPacket_ne_zero _ hβ
    have hz := h S
    rw [orderedStarCouplingDeriv_characterAction a ha mean k S] at hz
    have hfac : (-1 : ℝ) ^ S.card * (S.card.factorial : ℝ) *
        (a⁻¹) ^ (S.card + 1) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero S.card)
      · exact pow_ne_zero _ (inv_ne_zero (ne_of_gt ha))
    exact hS (by exact_mod_cast (mul_eq_zero.mp hz).resolve_left hfac)
  · intro h S
    rw [orderedStarCouplingDeriv_characterAction a ha mean k S]
    simp [integerStarWalshPacket, h]

/-- One common bounded diagonal reference field; no coefficient depends on a character or replica
order. Its ternary weights separate all computational configurations. -/
def starJetReferenceField (n : ℕ) (i : Fin n) : ℝ :=
  (3 : ℝ) ^ (i : ℕ) / (3 : ℝ) ^ n

theorem starJetReferenceField_pos_le_one (n : ℕ) (i : Fin n) :
    0 < starJetReferenceField n i ∧ starJetReferenceField n i ≤ 1 := by
  constructor
  · unfold starJetReferenceField
    positivity
  · unfold starJetReferenceField
    apply (div_le_one (by positivity : (0 : ℝ) < 3 ^ n)).mpr
    exact pow_le_pow_right₀ (by norm_num) i.isLt.le

def starJetReferenceEnergy (n : ℕ) (x : Fin n → Bool) : ℝ :=
  ∑ i, starJetReferenceField n i * siteSign x i

/-- The common base has simple spectrum, proved from the existing ternary separation theorem. -/
theorem starJetReferenceEnergy_injective (n : ℕ) :
    Function.Injective (starJetReferenceEnergy n) := by
  intro x y hxy
  by_contra hne
  have hsep := two_le_abs_sum_signDiff hne
  have hform (x : Fin n → Bool) :
      starJetReferenceEnergy n x =
        (∑ i : Fin n, (3 : ℝ) ^ (i : ℕ) * siteSign x i) / (3 : ℝ) ^ n := by
    simp only [starJetReferenceEnergy, starJetReferenceField, div_mul_eq_mul_div,
      Finset.sum_div]
  rw [hform, hform] at hxy
  have hpow : (3 : ℝ) ^ n ≠ 0 := by positivity
  have hraw := congrArg (fun v : ℝ => v * (3 : ℝ) ^ n) hxy
  simp only [div_mul_cancel₀ _ hpow] at hraw
  have hzero : (∑ i : Fin n, (3 : ℝ) ^ (i : ℕ) * (siteSign x i - siteSign y i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hraw, sub_self]
  rw [hzero, abs_zero] at hsep
  norm_num at hsep

/-- Spectral character restricted to the distinguished-spin slice through the same reference
field for every choice of spin. -/
def commonReferenceStarCharacterAction {n : ℕ}
    (k : (Fin n → Bool) → ℤ) (i : Fin n)
    (c : {j : Fin n // j ≠ i} → ℝ) (u : ℝ) : ℝ :=
  twoLocalStarCharacterAction (starJetReferenceField n i)
    (fun z => ∑ j : {j : Fin n // j ≠ i},
      starJetReferenceField n j * (if z j then -1 else 1))
    (fun p => k (edgeEquiv i p)) c u

private theorem sum_eq_site_add_environment {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    (∑ j, f j) = f i + ∑ j : {j : Fin n // j ≠ i}, f j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase i) (by intro j; simp) f

/-- All selected-spin spectral branches really start at the same labelled simple base. -/
theorem commonReferenceStarRoot_zero (n : ℕ) (i : Fin n)
    (p : Fin 2 × qubitEnvironment n i) :
    blockSplitRoot
      (fun z => ∑ j : {j : Fin n // j ≠ i},
        starJetReferenceField n j * (if z j then -1 else 1))
      (twoLocalStarGap (starJetReferenceField n i) 0) p 0 =
        starJetReferenceEnergy n (edgeEquiv i p) := by
  have ha := (starJetReferenceField_pos_le_one n i).1
  have hgap : twoLocalStarGap (starJetReferenceField n i)
      (0 : {j : Fin n // j ≠ i} → ℝ) =
        (fun _ : qubitEnvironment n i => starJetReferenceField n i) := by
    funext z
    simp [twoLocalStarGap]
  rw [hgap, blockSplitRoot_zero_eq _ _ (fun _ => ha)]
  rcases p with ⟨b, z⟩
  rw [starJetReferenceEnergy, sum_eq_site_add_environment _ i, edgeEquiv_apply]
  have hsite (j : {j : Fin n // j ≠ i}) :
      edgeState i z (finTwoEquiv b) j = z j :=
    edgeState_of_ne i z (finTwoEquiv b) j.property
  simp only [siteSign, edgeState_self, hsite, blockEnergy]
  fin_cases b <;> simp [finTwoEquiv] <;> ring

private theorem exists_edgePacket_ne_zero_of_balanced
    {n : ℕ} (k : (Fin n → Bool) → ℤ)
    (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ i : Fin n, (fun z : qubitEnvironment n i =>
      k (edgeState i z false) - k (edgeState i z true)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hpair : ∀ i z, k (edgeState i z false) = k (edgeState i z true) := by
    intro i z
    exact sub_eq_zero.mp (congrFun (h i) z)
  have htoggle : ∀ x i, k (boolToggle x i) = k x := by
    intro x i
    obtain ⟨⟨b, z⟩, rfl⟩ := (edgeEquiv i).surjective x
    fin_cases b
    · change k (boolToggle (edgeState i z false) i) = k (edgeState i z false)
      rw [boolToggle_edgeState]
      exact (hpair i z).symm
    · change k (boolToggle (edgeState i z true) i) = k (edgeState i z true)
      rw [boolToggle_edgeState]
      exact hpair i z
  let x₀ : Fin n → Bool := fun _ => false
  have hconstant := const_of_boolToggle_const k htoggle
  have hmass : (Fintype.card (Fin n → Bool) : ℤ) * k x₀ = 0 := by
    have heq : (∑ x, k x) = ∑ _x : Fin n → Bool, k x₀ :=
      Finset.sum_congr rfl (fun x _ => hconstant x x₀)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      heq.symm.trans hbalance
  have hcard : (Fintype.card (Fin n → Bool) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hbase : k x₀ = 0 := (mul_eq_zero.mp hmass).resolve_left hcard
  apply hk
  funext x
  exact (hconstant x x₀).trans hbase

/-- Every balanced nonzero integer character is detected at the same simple diagonal base by
at most `n+1` parameter derivatives, with absolute response at least one.  The reference base and
lower bound do not depend on replica order. This is a local source certificate, not an ensemble
coarea bound or a circuit exclusion theorem. -/
theorem balanced_integer_character_commonBase_starJet_detection
    (n : ℕ) (k : (Fin n → Bool) → ℤ)
    (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
      S.card + 2 ≤ n + 1 ∧
        1 ≤ |orderedStarCouplingDeriv S.toList
          (fun c => deriv (deriv (commonReferenceStarCharacterAction k i c)) 0) 0| := by
  obtain ⟨i, hi⟩ := exists_edgePacket_ne_zero_of_balanced k hbalance hk
  let a := starJetReferenceField n i
  let mean : qubitEnvironment n i → ℝ := fun z =>
    ∑ j : {j : Fin n // j ≠ i},
      starJetReferenceField n j * (if z j then -1 else 1)
  let packet : Fin 2 × qubitEnvironment n i → ℤ := fun p => k (edgeEquiv i p)
  have ha := starJetReferenceField_pos_le_one n i
  obtain ⟨S, hcard, hbound⟩ := exists_twoLocalStar_integerSpectralCurvature_detection
    a ha.1 (fun z => packet (0, z) - packet (1, z)) hi
    (∑ z, ((packet (0, z) : ℝ) + (packet (1, z) : ℝ)) * mean z)
  have henv : Fintype.card {j : Fin n // j ≠ i} < n := by
    simpa using Fintype.card_subtype_lt (x := i) (p := fun j : Fin n => j ≠ i)
      (by simp)
  refine ⟨i, S, by omega, ?_⟩
  have hinv : 1 ≤ a⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right ha.2 (inv_nonneg.mpr ha.1.le)
    rw [mul_inv_cancel₀ ha.1.ne', one_mul] at hh
    exact hh
  have hfac : (1 : ℝ) ≤ (S.card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos S.card
  have hp : (1 : ℝ) ≤ (a⁻¹) ^ (S.card + 1) := one_le_pow₀ hinv
  have hunit : (1 : ℝ) ≤ (S.card.factorial : ℝ) * (a⁻¹) ^ (S.card + 1) := by
    nlinarith
  have haction : commonReferenceStarCharacterAction k i =
      twoLocalStarCharacterAction a mean packet := rfl
  rw [haction]
  simp_rw [twoLocalStarCharacterAction_eq_relation]
  exact hunit.trans hbound

end

end GaloisForLFunctions.HTGeometry

