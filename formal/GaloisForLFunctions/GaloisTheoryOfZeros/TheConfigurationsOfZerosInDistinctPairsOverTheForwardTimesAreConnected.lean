import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroThatIsAContinuousFunctionOfFinitelyManyZerosIsOneOfThemUpToTheSign
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The configurations of zeros in distinct pairs over the forward times are connected

`forwardPairConfigurations n` is the set of the points `(τ, z₁, …, zₙ)` over the forward times
`τ` off the branch times with `H_τ(zᵢ) = 0` and no two `zᵢ` equal or opposite.

* **Connected** (`isPathConnected_forwardPairConfigurations`). Any two configurations are joined
  by a path of configurations. This is the topological form of multiple transitivity: the `n`-th
  fibre power of the cover of the zeros, without the diagonals and the antidiagonals, is
  irreducible for every `n`.
* **No polynomial relation persists** (`eq_zero_of_eval_eq_zero_on_forwardPairConfigurations`).
  Let `P_τ` be a polynomial in `n` variables for every time. If the set of the configurations
  with `P_τ(z₁, …, zₙ) = 0` is open and closed in the configurations and not empty, then
  `P_τ = 0` for every forward time off the branch times: zeros in distinct pairs are
  algebraically independent over the functions of the time.

Proof. Two lifts of a forward path that agree at one parameter agree at the start, so lifts that
start in distinct pairs stay in distinct pairs (`IsForwardPath.mem_forwardPairConfigurations`).
A forward path between the two times carries the first configuration to a configuration over the
second time, and one loop carries that to the second configuration
(`exists_mem_forwardMonodromy_forall_apply_eq`). A relation that persists holds on all
configurations; over one time the zeros whose pair number is `i` modulo `n` form an infinite set
for each `i`, and the product of these sets consists of configurations.
-/

open Complex Set Filter Topology
open RHTower Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-- The configurations of `n` zeros of `H_τ`, no two equal or opposite, over the forward times
off the branch times. -/
def forwardPairConfigurations (n : ℕ) : Set (ℂ × (Fin n → ℂ)) :=
  {x | x ∈ forwardConfigurations n ∧ ∀ i j, i ≠ j → x.2 j ≠ x.2 i ∧ x.2 j ≠ -x.2 i}

variable {n : ℕ}

/-! ## Paths of configurations -/

/-- Lifts of a forward path that start in distinct pairs stay in distinct pairs. -/
theorem IsForwardPath.mem_forwardPairConfigurations {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    {u : Fin n → ℝ → ℂ} (hu : ∀ i, IsZeroLift γ 1 (u i))
    (h0 : ∀ i j, i ≠ j → u j 0 ≠ u i 0 ∧ u j 0 ≠ -u i 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (γ s, fun i => u i s) ∈ forwardPairConfigurations n := by
  refine ⟨⟨hγ.re_pos s hs, hγ.simple s hs, fun i => (hu i).zero s hs⟩,
    fun i j hij => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (h0 i j hij).1
      (IsZeroLift.eq_zero_of_eq hγ.continuousOn hγ.simple (hu j) (hu i) hs h)
  · exact (h0 i j hij).2
      (IsZeroLift.eq_zero_of_eq hγ.continuousOn hγ.simple (hu j) (hu i).neg hs h)

/-- The lifts of a forward path join the configuration over its start to the one over its end. -/
theorem IsForwardPath.joinedIn_forwardPairConfigurations {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    {u : Fin n → ℝ → ℂ} (hu : ∀ i, IsZeroLift γ 1 (u i))
    (h0 : ∀ i j, i ≠ j → u j 0 ≠ u i 0 ∧ u j 0 ≠ -u i 0) :
    _root_.JoinedIn (forwardPairConfigurations n) (γ 0, fun i => u i 0) (γ 1, fun i => u i 1) :=
  _root_.JoinedIn.ofLine (f := fun s => (γ s, fun i => u i s))
    (hγ.continuousOn.prodMk (continuousOn_pi.2 fun i => (hu i).continuousOn)) rfl rfl (by
      rintro _ ⟨s, hs, rfl⟩
      exact hγ.mem_forwardPairConfigurations hu h0 hs)

/-- **Two configurations of zeros in distinct pairs are joined by a path of configurations.** -/
theorem joinedIn_forwardPairConfigurations {x y : ℂ × (Fin n → ℂ)}
    (hx : x ∈ forwardPairConfigurations n) (hy : y ∈ forwardPairConfigurations n) :
    _root_.JoinedIn (forwardPairConfigurations n) x y := by
  obtain ⟨τ, z⟩ := x
  obtain ⟨τ', z'⟩ := y
  obtain ⟨⟨hτ, hb, hz⟩, hzd⟩ : (0 < τ.re ∧ τ ∉ branchTimes ∧ ∀ i, complexHeat τ (z i) = 0) ∧
      ∀ i j, i ≠ j → z j ≠ z i ∧ z j ≠ -z i := hx
  obtain ⟨⟨hτ', hb', hz'⟩, hzd'⟩ : (0 < τ'.re ∧ τ' ∉ branchTimes ∧
      ∀ i, complexHeat τ' (z' i) = 0) ∧ ∀ i j, i ≠ j → z' j ≠ z' i ∧ z' j ≠ -z' i := hy
  -- a forward path between the two times carries the first configuration along
  obtain ⟨δ, hδ, h0, h1⟩ := exists_isForwardPath hτ hτ' hb hb'
  have hlift : ∀ i, ∃ u : ℝ → ℂ, IsZeroLift δ 1 u ∧ u 0 = z i := fun i =>
    exists_isZeroLift_of_re_pos hδ.continuousOn hδ.re_pos hδ.simple (by rw [h0]; exact hz i)
  choose u hu hu0 using hlift
  have e0 : (fun i => u i 0) = z := funext hu0
  have hd0 : ∀ i j, i ≠ j → u j 0 ≠ u i 0 ∧ u j 0 ≠ -u i 0 := fun i j hij => by
    rw [hu0 i, hu0 j]
    exact hzd i j hij
  have hJ1 := hδ.joinedIn_forwardPairConfigurations hu hd0
  rw [h0, h1, e0] at hJ1
  have hw := hδ.mem_forwardPairConfigurations hu hd0 (right_mem_Icc.2 zero_le_one)
  rw [h1] at hw
  obtain ⟨⟨-, -, hwz⟩, hwd⟩ : (0 < τ'.re ∧ τ' ∉ branchTimes ∧
      ∀ i, complexHeat τ' (u i 1) = 0) ∧ ∀ i j, i ≠ j → u j 1 ≠ u i 1 ∧ u j 1 ≠ -u i 1 := hw
  -- one loop carries it to the second configuration
  obtain ⟨g, hg, hgq⟩ := exists_mem_forwardMonodromy_forall_apply_eq hτ' hb'
    (p := fun i => ⟨u i 1, hwz i⟩) (q := fun i => ⟨z' i, hz' i⟩)
    (fun i j hij => ⟨fun h => (hwd i j hij).1 (congrArg Subtype.val h),
      fun h => (hwd i j hij).2 (congrArg Subtype.val h)⟩)
    (fun i j hij => ⟨fun h => (hzd' i j hij).1 (congrArg Subtype.val h),
      fun h => (hzd' i j hij).2 (congrArg Subtype.val h)⟩)
  have hgq' : ∀ i, g ⟨u i 1, hwz i⟩ = ⟨z' i, hz' i⟩ := hgq
  obtain ⟨γ, hγ, g0, g1, hT⟩ := hg
  have hlift2 : ∀ i, ∃ v : ℝ → ℂ, IsZeroLift γ 1 v ∧ v 0 = u i 1 ∧ v 1 = z' i := fun i => by
    have h := hT ⟨u i 1, hwz i⟩
    rw [hgq' i] at h
    exact h
  choose v hv hv0 hv1 using hlift2
  have ev0 : (fun i => v i 0) = fun i => u i 1 := funext hv0
  have ev1 : (fun i => v i 1) = z' := funext hv1
  have hd1 : ∀ i j, i ≠ j → v j 0 ≠ v i 0 ∧ v j 0 ≠ -v i 0 := fun i j hij => by
    rw [hv0 i, hv0 j]
    exact hwd i j hij
  have hJ2 := hγ.joinedIn_forwardPairConfigurations hv hd1
  rw [g0, g1, ev0, ev1] at hJ2
  exact hJ1.trans hJ2

private theorem eighth_forward' :
    0 < (((1 / 8 : ℝ) : ℂ)).re ∧ ((1 / 8 : ℝ) : ℂ) ∉ branchTimes :=
  ⟨by rw [Complex.ofReal_re]; norm_num, ofReal_not_mem_branchTimes_of_eighth_le le_rfl⟩

theorem nonempty_forwardPairConfigurations (n : ℕ) : (forwardPairConfigurations n).Nonempty := by
  obtain ⟨P, hP, hG⟩ :=
    exists_pairCoordinate_isWindowedSignedGroup eighth_forward'.1 eighth_forward'.2
  choose p hp using fun i : Fin n => hG.surjective ((i : ℕ) : ℤ)
  refine ⟨(((1 / 8 : ℝ) : ℂ), fun i => (p i).1),
    ⟨eighth_forward'.1, eighth_forward'.2, fun i => (p i).2⟩,
    fun i j hij => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have e : p j = p i := Subtype.ext h
    have e' := congrArg P.pair e
    rw [hp, hp] at e'
    exact hij (Fin.ext (by exact_mod_cast e'.symm))
  · have e : p j = P.flip (p i) := by
      rw [hP]
      exact Subtype.ext h
    have e' := congrArg P.pair e
    rw [P.pair_flip, hp, hp] at e'
    exact hij (Fin.ext (by exact_mod_cast e'.symm))

/-- **The configurations of `n` zeros in distinct pairs over the forward times are path
connected.** -/
theorem isPathConnected_forwardPairConfigurations (n : ℕ) :
    IsPathConnected (forwardPairConfigurations n) := by
  obtain ⟨x, hx⟩ := nonempty_forwardPairConfigurations n
  exact ⟨x, hx, fun y hy => joinedIn_forwardPairConfigurations hx hy⟩

theorem isConnected_forwardPairConfigurations (n : ℕ) :
    IsConnected (forwardPairConfigurations n) :=
  (isPathConnected_forwardPairConfigurations n).isConnected

/-! ## No polynomial relation persists -/

/-- Over one forward time off the branch times, a polynomial that vanishes at every configuration
of zeros in distinct pairs is zero. -/
theorem eq_zero_of_forall_eval_eq_zero {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes)
    {p : MvPolynomial (Fin n) ℂ}
    (h : ∀ z : Fin n → ℂ, (τ, z) ∈ forwardPairConfigurations n → MvPolynomial.eval z p = 0) :
    p = 0 := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hτ hb
  choose q hq using hG.surjective
  -- the zeros whose pair number is `i` modulo `n`
  refine MvPolynomial.funext_set
    (fun i : Fin n => {w : ℂ | ∃ x : {z : ℂ // complexHeat τ z = 0},
      x.1 = w ∧ P.pair x % (n : ℤ) = ((i : ℕ) : ℤ)}) (fun i => ?_) fun z hz => ?_
  · have hn : (n : ℤ) ≠ 0 := by
      have := i.pos
      exact_mod_cast this.ne'
    refine infinite_of_injective_forall_mem
      (f := fun k : ℕ => (q (((i : ℕ) : ℤ) + (k : ℤ) * (n : ℤ))).1) (fun k k' hk => ?_) fun k => ?_
    · have e := congrArg P.pair (Subtype.ext hk)
      rw [hq, hq] at e
      exact_mod_cast mul_right_cancel₀ hn (add_left_cancel e)
    · refine ⟨_, rfl, ?_⟩
      rw [hq, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)
  · rw [map_zero]
    choose x hx hxn using fun i => hz i (mem_univ i)
    refine h z ⟨⟨hτ, hb, fun i => by
      show complexHeat τ (z i) = 0
      rw [← hx i]
      exact (x i).2⟩, fun i j hij => ?_⟩
    have hne : P.pair (x j) ≠ P.pair (x i) := fun e => hij (Fin.ext (by
      have e' := hxn i
      rw [← e, hxn j] at e'
      exact_mod_cast e'.symm))
    refine ⟨fun e => hne ?_, fun e => hne ?_⟩
    · rw [show x j = x i from Subtype.ext ((hx j).trans (e.trans (hx i).symm))]
    · rw [show x j = P.flip (x i) from by
        rw [hP]
        exact Subtype.ext ((hx j).trans (e.trans (congrArg Neg.neg (hx i).symm))), P.pair_flip]

/-- **No polynomial relation among zeros in distinct pairs persists.** Let `P_τ` be a polynomial
in `n` variables for every time. If the configurations with `P_τ(z₁, …, zₙ) = 0` form an open
and closed subset of the configurations of zeros in distinct pairs, and there is one, then
`P_τ = 0` for every forward time `τ` off the branch times. -/
theorem eq_zero_of_eval_eq_zero_on_forwardPairConfigurations {P : ℂ → MvPolynomial (Fin n) ℂ}
    (hopen : ∀ x ∈ forwardPairConfigurations n, MvPolynomial.eval x.2 (P x.1) = 0 →
      ∀ᶠ y in 𝓝[forwardPairConfigurations n] x, MvPolynomial.eval y.2 (P y.1) = 0)
    (hclosed : ∀ x ∈ forwardPairConfigurations n, MvPolynomial.eval x.2 (P x.1) ≠ 0 →
      ∀ᶠ y in 𝓝[forwardPairConfigurations n] x, MvPolynomial.eval y.2 (P y.1) ≠ 0)
    (hne : ∃ x ∈ forwardPairConfigurations n, MvPolynomial.eval x.2 (P x.1) = 0) {τ : ℂ}
    (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) : P τ = 0 := by
  classical
  -- the relation is a locally constant function on the connected set of configurations
  have hf : ContinuousOn (fun x : ℂ × (Fin n → ℂ) =>
      decide (MvPolynomial.eval x.2 (P x.1) = 0)) (forwardPairConfigurations n) := by
    intro x hx
    by_cases h : MvPolynomial.eval x.2 (P x.1) = 0
    · exact (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : ℂ × (Fin n → ℂ) => true) _ x).congr_of_eventuallyEq
        ((hopen x hx h).mono fun y hy => decide_eq_true hy) (decide_eq_true h)
    · exact (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : ℂ × (Fin n → ℂ) => false) _ x).congr_of_eventuallyEq
        ((hclosed x hx h).mono fun y hy => decide_eq_false hy) (decide_eq_false h)
  obtain ⟨x₀, hx₀, h₀⟩ := hne
  refine eq_zero_of_forall_eval_eq_zero hτ hb fun z hz => ?_
  have e := (isConnected_forwardPairConfigurations n).isPreconnected.constant hf hx₀ hz
  exact of_decide_eq_true (e.symm.trans (decide_eq_true h₀))

end GaloisForLFunctions.GaloisTheoryOfZeros
