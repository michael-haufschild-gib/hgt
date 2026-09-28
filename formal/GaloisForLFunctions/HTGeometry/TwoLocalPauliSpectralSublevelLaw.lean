import GaloisForLFunctions.HTGeometry.TwoLocalPauliSpectralJetLaw
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Prop23
import GaloisForLFunctions.HTGeometry.SpectralCharacterReplicaHeightLaw

/-!
# Uniform sublevel bounds for two-local Pauli spectral actions

The full two-local Pauli family has a projective spectral germ of finite type at the
common diagonal reference matrix. The finite-type order is at most `n + 1`.
Applying the Kleinbock–Margulis good-function theorem gives exponent
`1 / (pauliSourceDimension n * (n + 1))` on a source ball. Compactness of the
normalized affine coefficient sphere removes the supremum from the bound.

For each fixed `n`, the same positive radius and constant work for every nonzero
balanced integer spectral character, hence for every replica order. This is a
bound for each character, not a bound for their union. The constants are
existential and may depend on `n`. No incidence action, observer-Jacobian,
fibre multiplicity, circuit-union, or first-return estimate is asserted here.
-/

open Filter Topology Set Metric MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
noncomputable section

noncomputable local instance sublevelBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

/-- Lift coefficients of differences from an anchor to a zero-sum covector. -/
def anchoredRealCovector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι) (w : {x : ι // x ≠ b} → ℝ) (x : ι) : ℝ :=
  ∑ j, w j * ((if (j : ι) = x then 1 else 0) - (if b = x then 1 else 0))

theorem sum_anchoredRealCovector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι) (w : {x : ι // x ≠ b} → ℝ) : ∑ x, anchoredRealCovector b w x = 0 := by
  unfold anchoredRealCovector
  rw [Finset.sum_comm]
  simp [mul_sub, Finset.sum_sub_distrib]

theorem anchoredRealCovector_apply_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι) (w : {x : ι // x ≠ b} → ℝ) (j : {x : ι // x ≠ b}) :
    anchoredRealCovector b w j = w j := by
  unfold anchoredRealCovector
  simp only [if_neg (Ne.symm j.property), sub_zero]
  have heq (a : {x : ι // x ≠ b}) : ((a : ι) = j) ↔ a = j := Subtype.ext_iff.symm
  simp [heq]

theorem sum_anchoredRealCovector_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι) (w : {x : ι // x ≠ b} → ℝ) (v : ι → ℝ) :
    ∑ x, anchoredRealCovector b w x * v x = ∑ j, w j * (v j - v b) := by
  simp only [anchoredRealCovector, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem anchoredRealCovector_eq_of_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι) (k : ι → ℝ) (hk : ∑ x, k x = 0) :
    anchoredRealCovector b (fun j => k j) = k := by
  let a := anchoredRealCovector b (fun j => k j)
  have hout (x : ι) (hx : x ≠ b) : a x = k x :=
    anchoredRealCovector_apply_ne b (fun j => k j) ⟨x, hx⟩
  have hsum : ∑ x, (a x - k x) = 0 := by
    rw [Finset.sum_sub_distrib, sum_anchoredRealCovector, hk, sub_self]
  have hb : a b - k b = 0 := by
    rw [Finset.sum_eq_single b (fun x _ hx => by rw [hout x hx, sub_self])
      (by simp)] at hsum
    exact hsum
  funext x
  by_cases hx : x = b
  · subst x
    exact sub_eq_zero.mp hb
  · exact hout x hx

/-- Dimension of the full real coefficient space of Pauli words of weight at most two. -/
def pauliSourceDimension (n : ℕ) : ℕ := Fintype.card (PauliBoundedLabel n 2)

/-- Reindex the full Pauli coefficient space by `Fin`, preserving its linear topology. -/
def pauliSourceEquiv (n : ℕ) :
    (Fin (pauliSourceDimension n) → ℝ) ≃L[ℝ] (PauliBoundedLabel n 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : PauliBoundedLabel n 2 => ℝ)
    (Fintype.equivFin (PauliBoundedLabel n 2)).symm

theorem pauliSourceDimension_pos (n : ℕ) : 0 < pauliSourceDimension n := by
  haveI : Nonempty (PauliBoundedLabel n 2) :=
    ⟨⟨pauliIdentityLabel n, by simp [pauliWeight, pauliIdentityLabel]⟩⟩
  exact Fintype.card_pos

def pauliSpectralAnchor (n : ℕ) : Fin n → Bool := fun _ => false

abbrev PauliSpectralTail (n : ℕ) := {x : Fin n → Bool // x ≠ pauliSpectralAnchor n}

def pauliSpectralTailEquiv (n : ℕ) :
    PauliSpectralTail n ≃ Fin (Fintype.card (PauliSpectralTail n)) := Fintype.equivFin _

/-- Real part of a labelled spectral germ in numbered full-source coordinates. -/
def numberedPauliSpectralLevel (n : ℕ) (x : Fin n → Bool)
    (p : Fin (pauliSourceDimension n) → ℝ) : ℝ :=
  (commonReferenceSpectralBranch n x
    (commonReferencePauliMatrix n (pauliSourceEquiv n p))).re

/-- Spectral differences from the fixed all-false anchor. -/
def pauliProjectiveSpectrum (n : ℕ) (p : Fin (pauliSourceDimension n) → ℝ)
    (j : Fin (Fintype.card (PauliSpectralTail n))) : ℝ :=
  numberedPauliSpectralLevel n ((pauliSpectralTailEquiv n).symm j).val p -
    numberedPauliSpectralLevel n (pauliSpectralAnchor n) p

def pauliBalancedLift (n : ℕ) (w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ) :
    (Fin n → Bool) → ℝ :=
  anchoredRealCovector (pauliSpectralAnchor n) (fun j => w (pauliSpectralTailEquiv n j))

theorem sum_pauliBalancedLift (n : ℕ) (w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ) :
    ∑ x, pauliBalancedLift n w x = 0 := sum_anchoredRealCovector _ _

theorem pauliBalancedLift_ne_zero (n : ℕ)
    {w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ} (hw : w ≠ 0) :
    pauliBalancedLift n w ≠ 0 := by
  intro hk
  apply hw
  funext j
  have hj := congrFun hk ((pauliSpectralTailEquiv n).symm j).val
  simpa [pauliBalancedLift, anchoredRealCovector_apply_ne] using hj

theorem pauliProjective_comb_eq (n : ℕ)
    (w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ) :
    KleinbockMargulis.comb w (pauliProjectiveSpectrum n) =
      commonReferencePauliAction (pauliBalancedLift n w) ∘ pauliSourceEquiv n := by
  funext p
  change (∑ j, w j * pauliProjectiveSpectrum n p j) =
    ∑ x, pauliBalancedLift n w x * numberedPauliSpectralLevel n x p
  rw [pauliBalancedLift, sum_anchoredRealCovector_mul]
  simpa only [pauliProjectiveSpectrum, Equiv.symm_apply_apply] using
    (pauliSpectralTailEquiv n).sum_comp (fun j => w j * pauliProjectiveSpectrum n p j) |>.symm

theorem contDiffAt_numberedPauliSpectralLevel (n : ℕ) (x : Fin n → Bool) :
    ContDiffAt ℝ ⊤ (numberedPauliSpectralLevel n x) 0 := by
  have hm : ContDiff ℝ ⊤ (commonReferencePauliMatrix n ∘ pauliSourceEquiv n) :=
    (contDiff_commonReferencePauliMatrix n).comp (pauliSourceEquiv n).contDiff
  have hb : ContDiffAt ℝ ⊤ (commonReferenceSpectralBranch n x)
      ((commonReferencePauliMatrix n ∘ pauliSourceEquiv n) 0) := by
    simpa only [Function.comp_apply, map_zero, commonReferencePauliMatrix_zero] using!
      ((commonReferenceSpectralBranch_spec n x).1.restrictScalars (𝕜 := ℝ)).contDiffAt
  exact Complex.reCLM.contDiff.contDiffAt.comp 0 (hb.comp 0 hm.contDiffAt)

theorem contDiffAt_pauliProjectiveSpectrum (n : ℕ) :
    ContDiffAt ℝ ⊤ (pauliProjectiveSpectrum n) 0 := by
  apply contDiffAt_pi.mpr
  intro j
  exact (contDiffAt_numberedPauliSpectralLevel n _).sub
    (contDiffAt_numberedPauliSpectralLevel n _)

private theorem iteratedFDeriv_comp_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] F) (f : F → ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (f ∘ L) 0 =
      (iteratedFDeriv ℝ j f 0).compContinuousLinearMap (fun _ => L.toContinuousLinearMap) := by
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] using!
    L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := 0) (Set.mem_univ _) j

/-- Positive-order derivatives through order `n + 1` span the projective spectral target.
The conclusion follows from the concrete Pauli jet certificate, not an assumed rank condition. -/
theorem pauliProjectiveSpectrum_finiteType (n : ℕ) :
    ∀ w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ,
      (∀ j : ℕ, 1 ≤ j → j ≤ n + 1 → ∀ m : Fin j → (Fin (pauliSourceDimension n) → ℝ),
        ∑ a, w a * (iteratedFDeriv ℝ j (pauliProjectiveSpectrum n) 0 m) a = 0) → w = 0 := by
  intro w hw
  by_contra hw0
  let k := pauliBalancedLift n w
  have hk : k ≠ 0 := pauliBalancedLift_ne_zero n hw0
  obtain ⟨i, S, horder, hdetect⟩ := balanced_real_character_fullPauli_jet_detection n k
    (sum_pauliBalancedLift n w) hk
  let j := (starSpectralJetWord S).length
  let dirs : Fin j → (PauliBoundedLabel n 2 → ℝ) :=
    fun a => starPauliDirectionMap i (Pi.single ((starSpectralJetWord S).get a) 1)
  have hj : 1 ≤ j := by simp [j, starSpectralJetWord]
  have hzero := hw j hj horder (fun a => (pauliSourceEquiv n).symm (dirs a))
  have hsmooth : ContDiffAt ℝ (j : ℕ) (pauliProjectiveSpectrum n) 0 :=
    (contDiffAt_pauliProjectiveSpectrum n).of_le le_top
  rw [← KleinbockMargulis.iteratedFDeriv_comb hsmooth] at hzero
  rw [pauliProjective_comb_eq, iteratedFDeriv_comp_equiv] at hzero
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hzero
  change iteratedFDeriv ℝ j (commonReferencePauliAction k) 0 dirs = 0 at hzero
  change Real.sqrt (∑ x, k x ^ (2 : ℕ)) ≤
    |iteratedFDeriv ℝ j (commonReferencePauliAction k) 0 dirs| at hdetect
  rw [hzero, abs_zero] at hdetect
  have hpos : 0 < ∑ x, k x ^ (2 : ℕ) := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hk
    apply Finset.sum_pos' (fun x _ => sq_nonneg (k x))
    exact ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero hx⟩
  exact (not_le_of_gt (Real.sqrt_pos.2 hpos)) hdetect

/-- All affine combinations of the projective spectral germ are uniformly good
on one source neighborhood, by Kleinbock–Margulis Proposition 3.4. -/
theorem pauliProjectiveSpectrum_uniform_good (n : ℕ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (c : ℝ) (w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ),
        KleinbockMargulis.IsGood C (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)
          (fun p => c + KleinbockMargulis.comb w (pauliProjectiveSpectrum n) p) (ball 0 ρ) := by
  haveI : NeZero (pauliSourceDimension n) := ⟨(pauliSourceDimension_pos n).ne'⟩
  have hs : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ) (pauliProjectiveSpectrum n) 0 :=
    (contDiffAt_pauliProjectiveSpectrum n).of_le le_top
  have he := hs.eventually (by simp)
  obtain ⟨U, hU, hopen, hmem⟩ := _root_.mem_nhds_iff.mp he
  exact KleinbockMargulis.prop_3_4 (by omega) hopen
    (fun p hp => hU hp) hmem (pauliProjectiveSpectrum_finiteType n)

/-- The same good-function estimate in balanced spectral-character coordinates. -/
theorem pauliBalancedAction_uniform_good (n : ℕ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ (c : ℝ) (k : (Fin n → Bool) → ℝ),
      (∑ x, k x = 0) →
      KleinbockMargulis.IsGood C (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)
        (fun p => c + commonReferencePauliAction k (pauliSourceEquiv n p)) (ball 0 ρ) := by
  obtain ⟨ρ, C, hρ, hC, hg⟩ := pauliProjectiveSpectrum_uniform_good n
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro c k hk
  let w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ :=
    fun j => k ((pauliSpectralTailEquiv n).symm j).val
  have hlift : pauliBalancedLift n w = k := by
    simpa only [pauliBalancedLift, w, Equiv.symm_apply_apply] using
      anchoredRealCovector_eq_of_sum_zero (pauliSpectralAnchor n) k hk
  refine (hg c w).congr ?_
  intro p
  rw [pauliProjective_comb_eq, hlift]
  rfl

/-- Absolute sublevel estimate for every normalized affine spectral combination.
The source radius and constant do not depend on the affine coefficients. -/
theorem pauliProjectiveSpectrum_uniform_smallBall (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ (c : ℝ) (w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ),
        1 ≤ ‖(Fin.cons c w : Fin (Fintype.card (PauliSpectralTail n) + 1) → ℝ)‖ →
          ∀ ε : ℝ, 0 < ε →
          volume.real {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
            |c + KleinbockMargulis.comb w (pauliProjectiveSpectrum n) p| < ε} ≤
              K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹) *
                volume.real (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) := by
  obtain ⟨R, C, hR, hC, hgood⟩ := pauliProjectiveSpectrum_uniform_good n
  have hsmooth : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ) (pauliProjectiveSpectrum n) 0 :=
    (contDiffAt_pauliProjectiveSpectrum n).of_le le_top
  obtain ⟨s, hs, hlocal⟩ := Metric.mem_nhds_iff.mp (hsmooth.eventually (by simp))
  let ρ := min R s
  have hρ : 0 < ρ := lt_min hR hs
  have hindep := KleinbockMargulis.indep_of_nondegenerate
    (U := ball (0 : Fin (pauliSourceDimension n) → ℝ) s) (l := n + 1)
    (fun p hp => hlocal hp) (pauliProjectiveSpectrum_finiteType n) hρ
    (ball_subset_ball (min_le_right R s))
  obtain ⟨δ, hδ, hsup⟩ := KleinbockMargulis.exists_supGe hindep
  let α : ℝ := ((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹
  have hα : 0 < α := by
    dsimp [α]
    exact inv_pos.mpr (mul_pos (Nat.cast_pos.mpr (pauliSourceDimension_pos n))
      (Nat.cast_pos.mpr (Nat.succ_pos n)))
  let β := δ / 2
  have hβ : 0 < β := half_pos hδ
  have hpow : 0 < β ^ α := Real.rpow_pos_of_pos hβ α
  refine ⟨ρ, C / β ^ α, hρ, div_pos hC hpow, ?_⟩
  intro c w hw ε hε
  obtain ⟨z, hz, hβz⟩ := hsup (Fin.cons c w) hw β (by dsimp [β]; linarith)
  simp only [Fin.cons_zero, Fin.cons_succ] at hβz
  have hg := (hgood c w).mono_set (ball_subset_ball (min_le_left R s))
  have hmeasure := hg.toReal_le hC.le 0 hρ (Subset.refl _) hε hz
  have hmono := Real.rpow_le_rpow hβ.le hβz.le hα.le
  have hbound := (mul_le_mul_of_nonneg_left hmono
    (show 0 ≤ volume.real {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
      |c + KleinbockMargulis.comb w (pauliProjectiveSpectrum n) p| < ε} from
        ENNReal.toReal_nonneg)).trans hmeasure
  calc
    _ ≤ (C * ε ^ α * volume.real (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ)) /
        β ^ α := (le_div_iff₀ hpow).mpr hbound
    _ = _ := by ring

/-- Every nonzero balanced integer character satisfies one uniform local small-ball bound.
There is no upper bound on the character coefficients and the translation is arbitrary. -/
theorem pauliBalancedIntegerAction_uniform_smallBall (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ (c : ℝ) (k : (Fin n → Bool) → ℤ), SpectralCharacterBalanced k → k ≠ 0 →
        ∀ ε : ℝ, 0 < ε →
          volume.real {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
            |c + commonReferencePauliAction (fun x => (k x : ℝ)) (pauliSourceEquiv n p)| < ε} ≤
              K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹) *
                volume.real (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) := by
  obtain ⟨ρ, K, hρ, hK, hsmall⟩ := pauliProjectiveSpectrum_uniform_smallBall n
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro c k hbalance hk ε hε
  let w : Fin (Fintype.card (PauliSpectralTail n)) → ℝ :=
    fun j => (k ((pauliSpectralTailEquiv n).symm j).val : ℝ)
  have hsum : ∑ x, (k x : ℝ) = 0 := by exact_mod_cast hbalance
  have hlift : pauliBalancedLift n w = fun x => (k x : ℝ) := by
    simpa only [pauliBalancedLift, w, Equiv.symm_apply_apply] using
      anchoredRealCovector_eq_of_sum_zero (pauliSpectralAnchor n) (fun x => (k x : ℝ)) hsum
  have hw : w ≠ 0 := by
    intro hw0
    have hzero : pauliBalancedLift n w = 0 := by
      rw [hw0]
      funext x
      simp [pauliBalancedLift, anchoredRealCovector]
    rw [hlift] at hzero
    apply hk
    funext x
    have hx := congrFun hzero x
    change (k x : ℝ) = 0 at hx
    change k x = 0
    exact_mod_cast hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hjk : k ((pauliSpectralTailEquiv n).symm j).val ≠ 0 := by
    intro h
    apply hj
    simp [w, h]
  have hjunit : 1 ≤ |w j| := by
    change 1 ≤ |(k ((pauliSpectralTailEquiv n).symm j).val : ℝ)|
    exact_mod_cast Int.one_le_abs hjk
  have hnorm : 1 ≤ ‖(Fin.cons c w : Fin (Fintype.card (PauliSpectralTail n) + 1) → ℝ)‖ := by
    apply hjunit.trans
    simpa only [Real.norm_eq_abs, Fin.cons_succ] using
      norm_le_pi_norm
        (Fin.cons c w : Fin (Fintype.card (PauliSpectralTail n) + 1) → ℝ) j.succ
  have hbound := hsmall c w hnorm ε hε
  have heq (p : Fin (pauliSourceDimension n) → ℝ) :
      c + KleinbockMargulis.comb w (pauliProjectiveSpectrum n) p =
        c + commonReferencePauliAction (fun x => (k x : ℝ)) (pauliSourceEquiv n p) := by
    rw [pauliProjective_comb_eq, hlift]
    rfl
  simpa only [heq] using hbound

/-- One radius and one constant work separately for every nonzero replica character,
with all replica orders quantified after the constants. This does not estimate a union. -/
theorem pauliReplicaAction_allOrders_smallBall (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ (r : ℕ) (c : ℝ) (k : (Fin n → Bool) → ℤ),
        SpectralCharacterReplicaRealizes r k → k ≠ 0 → ∀ ε : ℝ, 0 < ε →
          volume.real {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
            |c + commonReferencePauliAction (fun x => (k x : ℝ)) (pauliSourceEquiv n p)| < ε} ≤
              K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹) *
                volume.real (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) := by
  obtain ⟨ρ, K, hρ, hK, hsmall⟩ := pauliBalancedIntegerAction_uniform_smallBall n
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro r c k hreal hk ε hε
  apply hsmall c k ?_ hk ε hε
  obtain ⟨p, q, hp, hq, hfreq⟩ := hreal
  unfold SpectralCharacterBalanced
  simp_rw [hfreq, Finset.sum_sub_distrib, ← Nat.cast_sum, hp, hq, sub_self]

end
end GaloisForLFunctions.HTGeometry
