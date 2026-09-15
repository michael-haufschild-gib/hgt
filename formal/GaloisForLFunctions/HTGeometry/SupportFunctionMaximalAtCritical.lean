/-
The exponent-pair support function is maximal exactly at the critical length.

For a family of exponent pairs indexed by a nonempty finite set, put

    h(x) := min over the family of  demand(κ, λ, x) = κ·(1 - x) + x·(λ - 1/2).

`h` is the support function of the family in the direction `(1 - x, x)`, and `h(1/2)` is the best
pointwise subconvexity exponent the family delivers.

If the family is closed under the van der Corput `B`-process — which every exponent-pair region is,
since `B` maps pairs to pairs and is an involution — then, because `B` acts on the length variable as
the reflection `x ↦ 1 - x` (the length-reflection law), the support function is symmetric:
`h(x) = h(1 - x)`.  Combined with the fact that a pair on or above the line of symmetry only improves
as the length shrinks, this gives

    **h(x) ≤ h(1/2)  for every length x,**

so the critical length is exactly where the family is *hardest*.  Every other length is easier, and
that is the structural reason the subconvexity exponent is the family's worst case rather than a
typical value.

Since `h ≥ 0` on the exponent-pair region, `h(1/2) = 0` forces `h ≡ 0`: the Lindelöf exponent is
attainable only if the support function degenerates completely, i.e. only if the family reaches the
corner `(0, 1/2)`.
-/
import GaloisForLFunctions.HTGeometry.CoveringCannotReachLindelof

namespace HTGeometry

open Finset

variable {ι : Type*}

/-- The support function of a finite family of exponent pairs: the best demand at length `T^x`. -/
noncomputable def supportFn (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ) (x : ℚ) : ℚ :=
  S.inf' hS fun i => covDemandOfPair x (κ i) (lam i)

/-- Every member's demand bounds the support function from above. -/
theorem supportFn_le (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ) (x : ℚ)
    {i : ι} (hi : i ∈ S) :
    supportFn S hS κ lam x ≤ covDemandOfPair x (κ i) (lam i) :=
  Finset.inf'_le _ hi

/-- The support function is attained. -/
theorem supportFn_attained (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ) (x : ℚ) :
    ∃ i ∈ S, supportFn S hS κ lam x = covDemandOfPair x (κ i) (lam i) :=
  Finset.exists_mem_eq_inf' hS _

/-- **Midpoint concavity of the variational support value.**  This is the finite-dimensional
ground-energy concavity mechanism from Fredheim--Kvaal, arXiv:2510.12242, applied to the corpus's
infimum of affine exponent-pair demands. -/
theorem supportFn_midpoint_concave (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (x y : ℚ) :
    (supportFn S hS κ lam x + supportFn S hS κ lam y) / 2 ≤
      supportFn S hS κ lam ((x + y) / 2) := by
  apply Finset.le_inf'
  intro i hi
  have hx := supportFn_le S hS κ lam x hi
  have hy := supportFn_le S hS κ lam y hi
  simp only [covDemandOfPair, covFunctional] at hx hy ⊢
  linarith

/-- Largest absolute affine slope among the competing exponent-pair demands. -/
noncomputable def supportSlopeBound (S : Finset ι) (hS : S.Nonempty)
    (κ lam : ι → ℚ) : ℚ :=
  S.sup' hS fun i => |epDisplacement (κ i) (lam i)|

theorem abs_epDisplacement_le_supportSlopeBound
    (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ) {i : ι} (hi : i ∈ S) :
    |epDisplacement (κ i) (lam i)| ≤ supportSlopeBound S hS κ lam :=
  by
    simpa [supportSlopeBound] using
      (Finset.le_sup' (fun k => |epDisplacement (κ k) (lam k)|) hi)

/-- **Global Lipschitz bound for the variational support value.**  This is the finite-family
counterpart of Fredheim--Kvaal, arXiv:2510.12242, Lemma 6.3: the ground energy varies at most by the
largest available affine slope. -/
theorem abs_supportFn_sub_supportFn_le
    (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ) (x y : ℚ) :
    |supportFn S hS κ lam x - supportFn S hS κ lam y| ≤
      supportSlopeBound S hS κ lam * |x - y| := by
  obtain ⟨i, hi, hxi⟩ := supportFn_attained S hS κ lam x
  obtain ⟨j, hj, hyj⟩ := supportFn_attained S hS κ lam y
  have hxy := supportFn_le S hS κ lam x hj
  have hyx := supportFn_le S hS κ lam y hi
  have hslope (k : ι) (hk : k ∈ S) (u v : ℚ) :
      epDisplacement (κ k) (lam k) * (u - v) ≤
        supportSlopeBound S hS κ lam * |u - v| := by
    calc
      epDisplacement (κ k) (lam k) * (u - v)
          ≤ |epDisplacement (κ k) (lam k) * (u - v)| := le_abs_self _
      _ = |epDisplacement (κ k) (lam k)| * |u - v| := abs_mul _ _
      _ ≤ supportSlopeBound S hS κ lam * |u - v| :=
        mul_le_mul_of_nonneg_right
          (abs_epDisplacement_le_supportSlopeBound S hS κ lam hk) (abs_nonneg _)
  have hupper : supportFn S hS κ lam x - supportFn S hS κ lam y ≤
      supportSlopeBound S hS κ lam * |x - y| := by
    calc
      supportFn S hS κ lam x - supportFn S hS κ lam y
          ≤ covDemandOfPair x (κ j) (lam j) - covDemandOfPair y (κ j) (lam j) := by
            rw [hyj]
            exact sub_le_sub_right hxy _
      _ = epDisplacement (κ j) (lam j) * (x - y) := by
        rw [covDemand_factorisation, covDemand_factorisation]
        ring
      _ ≤ supportSlopeBound S hS κ lam * |x - y| := hslope j hj x y
  have hlower : supportFn S hS κ lam y - supportFn S hS κ lam x ≤
      supportSlopeBound S hS κ lam * |x - y| := by
    calc
      supportFn S hS κ lam y - supportFn S hS κ lam x
          ≤ covDemandOfPair y (κ i) (lam i) - covDemandOfPair x (κ i) (lam i) := by
            rw [hxi]
            exact sub_le_sub_right hyx _
      _ = epDisplacement (κ i) (lam i) * (y - x) := by
        rw [covDemand_factorisation, covDemand_factorisation]
        ring
      _ ≤ supportSlopeBound S hS κ lam * |y - x| := hslope i hi y x
      _ = supportSlopeBound S hS κ lam * |x - y| := by rw [abs_sub_comm]
  rw [abs_le]
  constructor
  · linarith
  · exact hupper

/-- At the critical length the support function is the family's best pointwise exponent. -/
theorem supportFn_at_critical (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ) :
    supportFn S hS κ lam (1 / 2) = S.inf' hS fun i => epMu (κ i) (lam i) := by
  unfold supportFn
  exact Finset.inf'_congr hS rfl fun i _ => displacement_free_at_critical_length (κ i) (lam i)

/-- Closure of a family under the `B`-process. -/
def BClosed (S : Finset ι) (κ lam : ι → ℚ) : Prop :=
  ∀ i ∈ S, ∃ j ∈ S, κ j = procB_fst (lam i) ∧ lam j = procB_snd (κ i)

/-- **The support function is maximal at the critical length.**  For a `B`-closed family, no length
is harder than the critical one. -/
theorem supportFn_le_at_critical (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hclosed : BClosed S κ lam) {x : ℚ} (hx : x ≤ 1 / 2) :
    supportFn S hS κ lam x ≤ supportFn S hS κ lam (1 / 2) := by
  obtain ⟨i, hi, hval⟩ := supportFn_attained S hS κ lam (1 / 2)
  rw [hval, displacement_free_at_critical_length]
  by_cases hd : 0 ≤ epDisplacement (κ i) (lam i)
  · calc supportFn S hS κ lam x ≤ covDemandOfPair x (κ i) (lam i) := supportFn_le S hS κ lam x hi
      _ ≤ epMu (κ i) (lam i) := single_pair_covers_at_mu hd hx
  · obtain ⟨j, hj, hκj, hlamj⟩ := hclosed i hi
    have hdemand : covDemandOfPair x (κ j) (lam j) = covDemandOfPair (1 - x) (κ i) (lam i) := by
      rw [hκj, hlamj]; exact procB_is_length_reflection x (κ i) (lam i)
    have hle : covDemandOfPair (1 - x) (κ i) (lam i) ≤ epMu (κ i) (lam i) := by
      rw [covDemand_factorisation]
      have : epDisplacement (κ i) (lam i) * (1 - x - 1 / 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) (by linarith)
      linarith
    calc supportFn S hS κ lam x ≤ covDemandOfPair x (κ j) (lam j) := supportFn_le S hS κ lam x hj
      _ = covDemandOfPair (1 - x) (κ i) (lam i) := hdemand
      _ ≤ epMu (κ i) (lam i) := hle

/-- **The support function is symmetric about the critical length.** -/
theorem supportFn_reflect (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hclosed : BClosed S κ lam) (x : ℚ) :
    supportFn S hS κ lam (1 - x) ≤ supportFn S hS κ lam x := by
  obtain ⟨i, hi, hval⟩ := supportFn_attained S hS κ lam x
  obtain ⟨j, hj, hκj, hlamj⟩ := hclosed i hi
  have hdemand : covDemandOfPair (1 - x) (κ j) (lam j) = covDemandOfPair x (κ i) (lam i) := by
    rw [hκj, hlamj, procB_is_length_reflection]
    congr 1
    ring
  calc supportFn S hS κ lam (1 - x)
      ≤ covDemandOfPair (1 - x) (κ j) (lam j) := supportFn_le S hS κ lam (1 - x) hj
    _ = covDemandOfPair x (κ i) (lam i) := hdemand
    _ = supportFn S hS κ lam x := hval.symm

/-- A `B`-closed family has exact reflection symmetry. -/
theorem supportFn_reflect_eq (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hclosed : BClosed S κ lam) (x : ℚ) :
    supportFn S hS κ lam (1 - x) = supportFn S hS κ lam x := by
  apply le_antisymm
  · exact supportFn_reflect S hS κ lam hclosed x
  · have h := supportFn_reflect S hS κ lam hclosed (1 - x)
    have hx : (1 : ℚ) - (1 - x) = x := by ring
    rwa [hx] at h

/-- **Hence the maximality holds at every length, not only below the critical one.** -/
theorem supportFn_global_max (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hclosed : BClosed S κ lam) (x : ℚ) :
    supportFn S hS κ lam x ≤ supportFn S hS κ lam (1 / 2) := by
  have hmid := supportFn_midpoint_concave S hS κ lam x (1 - x)
  rw [supportFn_reflect_eq S hS κ lam hclosed x] at hmid
  have hx : (x + (1 - x)) / 2 = (1 / 2 : ℚ) := by ring
  rw [hx] at hmid
  linarith

/-! ### Nonnegativity and the degeneration -/

/-- The support function is nonnegative on the exponent-pair region. -/
theorem supportFn_nonneg (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hκ : ∀ i ∈ S, 0 ≤ κ i) (hlam : ∀ i ∈ S, 1 / 2 ≤ lam i)
    {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ supportFn S hS κ lam x := by
  apply Finset.le_inf'
  intro i hi
  exact covDemand_nonneg (hκ i hi) (hlam i hi) h0 h1

/-- **The Lindelöf exponent degenerates the whole support function.**  If the family attains
demand `0` at the critical length, it attains `0` at every length. -/
theorem lindelof_degenerates_support (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hclosed : BClosed S κ lam) (hκ : ∀ i ∈ S, 0 ≤ κ i) (hlam : ∀ i ∈ S, 1 / 2 ≤ lam i)
    (hcrit : supportFn S hS κ lam (1 / 2) = 0)
    {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    supportFn S hS κ lam x = 0 := by
  have hub := supportFn_global_max S hS κ lam hclosed x
  rw [hcrit] at hub
  have hlb := supportFn_nonneg S hS κ lam hκ hlam h0 h1
  linarith

/-- And then some member of the family is the corner `(0, 1/2)`. -/
theorem lindelof_forces_corner (S : Finset ι) (hS : S.Nonempty) (κ lam : ι → ℚ)
    (hκ : ∀ i ∈ S, 0 ≤ κ i) (hlam : ∀ i ∈ S, 1 / 2 ≤ lam i)
    {x : ℚ} (h0 : 0 < x) (h1 : x < 1) (hzero : supportFn S hS κ lam x = 0) :
    ∃ i ∈ S, κ i = 0 ∧ lam i = 1 / 2 := by
  obtain ⟨i, hi, hval⟩ := supportFn_attained S hS κ lam x
  refine ⟨i, hi, ?_⟩
  have : covDemandOfPair x (κ i) (lam i) = 0 := by rw [← hval, hzero]
  exact (covDemand_eq_zero_iff (hκ i hi) (hlam i hi) h0 h1).mp this

/-! ### The published families -/

/-- The subconvexity record is the support function's value at the critical length, and the
`A`-image data of cycle 210 exhibits it as a strict maximum against a shorter length. -/
theorem record_is_a_maximum :
    covDemandOfPair (1 / 2) bourgainKappa bourgainLambda = bourgainTheta ∧
      covDemandOfPair huxleyStart (procA_fst huxleyPairKappa)
          (procA_snd huxleyPairKappa huxleyPairLambda) < bourgainTheta ∧
      covDemandOfPair huxleyStart (procA_fst bourgainKappa)
          (procA_snd bourgainKappa bourgainLambda) < bourgainTheta := by
  refine ⟨?_, ?_, ?_⟩
  · rw [displacement_free_at_critical_length, bourgain_pair_mu]
  · rw [procA_huxleyPair_demand_at_huxleyStart]; unfold bourgainTheta; norm_num
  · rw [procA_bourgain_demand]; unfold bourgainTheta; norm_num

/-- **A single estimate valid at every length reaches the Lindelöf exponent only by being it.**  An
estimate `S(M) ≤ M^α T^β` valid for all `M ≤ T^(1/2)` yields `μ(1/2) ≤ 0` only if `β = 0` and
`α ≤ 1/2`. -/
theorem unrestricted_estimate_must_be_lindelof {α β : ℚ}
    (h0 : coveringDemand α β 0 ≤ 0) (hhalf : coveringDemand α β (1 / 2) ≤ 0) (hβ : 0 ≤ β) :
    β = 0 ∧ α ≤ 1 / 2 := by
  unfold coveringDemand at h0 hhalf
  constructor
  · linarith
  · nlinarith

end HTGeometry
