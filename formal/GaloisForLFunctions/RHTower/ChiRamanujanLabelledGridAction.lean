import GaloisForLFunctions.RHTower.ChiRamanujanCriticalGridSource
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicCriticalAtoms
import GaloisForLFunctions.RHTower.ChiRamanujanTransverseProfileFibres

/-!
# Complete labelled local source and its full inverse profiles

The full local product for each distinguished prime reproduces its exact
integer Fourier multiplier. Both literal physical contractions transfer to
label exclusions on the complete covered Fourier cube. These exclusions
force the two base factors at the third prime. Every other prime coordinate
remains inside the exact cofactor profile; grouping and exact dephasing attach
the full axes and inverse-curve law. No signed asymptotic saving is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

/-- Full local grids in all three coordinates, with their distinguished labels. -/
def ramanujanLabelledTripleAction {P : Finset ℕ} (p q r : RamanujanGridPrime P) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
    ∑ z : RamanujanLocalGrid P,
      (ramanujanLabelledLocalGridWeight p x : ℂ)*(ramanujanLabelledLocalGridWeight q y : ℂ)*
        (ramanujanLabelledLocalGridWeight r z : ℂ)*
        F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,ramanujanLocalGridNode z)
  map_add' F G := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    ring

theorem ramanujanLabelledTripleAction_phase {P : Finset ℕ}
    (p q r : RamanujanGridPrime P) (n : ℤ × ℤ × ℤ) :
    ramanujanLabelledTripleAction p q r (ramanujanTripleFourierPhase n) =
      (ramanujanDistinguishedPrimeEntry P p.val n.1.natAbs : ℂ)*
      (ramanujanDistinguishedPrimeEntry P q.val n.2.1.natAbs : ℂ)*
      (ramanujanDistinguishedPrimeEntry P r.val n.2.2.natAbs : ℂ) := by
  rw [← ramanujanLabelledLocalGridWeight_fourier P p n.1,
    ← ramanujanLabelledLocalGridWeight_fourier P q n.2.1,
    ← ramanujanLabelledLocalGridWeight_fourier P r n.2.2]
  conv_rhs => rw [mul_assoc]
  simp only [ramanujanLabelledTripleAction,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.sum_mul,ramanujanTripleFourierPhase]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Summing all distinguished labels retains the complete finite source. -/
def ramanujanCompleteLabelledAction (P : Finset ℕ) : ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ p : RamanujanGridPrime P, ∑ q : RamanujanGridPrime P,
    ∑ r : RamanujanGridPrime P, ramanujanLabelledTripleAction p q r

private lemma entry_sum (P : Finset ℕ) (n : ℕ) :
    (∑ p : RamanujanGridPrime P, ramanujanDistinguishedPrimeEntry P p.val n) =
      ramanujanDistinguishedPrimeMultiplier P n := by
  have hu : (Finset.univ : Finset (RamanujanGridPrime P))=(P.filter Nat.Prime).attach := by
    ext
    simp
  rw [hu,Finset.sum_attach (P.filter Nat.Prime)
    (fun p => ramanujanDistinguishedPrimeEntry P p n)]
  rfl

theorem ramanujanCompleteLabelledAction_phase (P : Finset ℕ) (n : ℤ × ℤ × ℤ) :
    ramanujanCompleteLabelledAction P (ramanujanTripleFourierPhase n) =
      (ramanujanDistinguishedPrimeMultiplier P n.1.natAbs : ℂ)*
      (ramanujanDistinguishedPrimeMultiplier P n.2.1.natAbs : ℂ)*
      (ramanujanDistinguishedPrimeMultiplier P n.2.2.natAbs : ℂ) := by
  conv_rhs => rw [mul_assoc]
  simp only [ramanujanCompleteLabelledAction,LinearMap.sum_apply,ramanujanLabelledTripleAction_phase,
    ← entry_sum,Complex.ofReal_sum,Finset.sum_mul]
  simp only [Finset.mul_sum,mul_assoc]

private lemma multiplier_band (M : ℕ) {n : ℕ} (hn : 1 < n) (hnM : n ≤ M) :
    (ramanujanDistinguishedPrimeMultiplier (Finset.range (M+1)) n : ℂ) =
      ((if n.Prime then Real.log n else 0 : ℝ) : ℂ) := by
  have h := (sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished
    (Finset.range (M+1)) (n : ℤ)).symm.trans
      (sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hn hnM)
  simpa only [Int.natAbs_natCast] using h

/-- Exact replacement on the complete covered cube, with both original projectors. -/
theorem ramanujanCompleteLabelledAction_projected_cube (M : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 < n ∧ n ≤ M) (c : ℕ → ℕ → ℕ → ℂ) :
    ramanujanCompleteLabelledAction (Finset.range (M+1))
      (ramanujanNoncontractingProjector (M+1) (ramanujanFiniteCubeTest S c)) =
    ramanujanCriticalTripleAtomAction (Finset.range (M+1))
      (ramanujanNoncontractingProjector (M+1) (ramanujanFiniteCubeTest S c)) := by
  unfold ramanujanFiniteCubeTest
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [ramanujanNoncontractingProjector_nat_phase M (hS p hp).2 (hS q hq).2 (hS r hr).2]
  split_ifs
  · simp only [map_zero,smul_zero]
  · rw [ramanujanCompleteLabelledAction_phase,
      ramanujanCriticalTripleAtomAction_nat_phase M (hS p hp).1 (hS q hq).1 (hS r hr).1
        (hS p hp).2 (hS q hq).2 (hS r hr).2]
    simp only [Int.natAbs_natCast,multiplier_band M (hS p hp).1 (hS p hp).2,
      multiplier_band M (hS q hq).1 (hS q hq).2,multiplier_band M (hS r hr).1 (hS r hr).2,
      Complex.ofReal_mul]

/-- The two physical exclusions become the same two distinguished-label exclusions. -/
theorem ramanujanLabelledTripleAction_projected_phase (M : ℕ)
    (p q r : RamanujanBandPrime M) (a b c : RamanujanCoveredCoordinate M) :
    ramanujanLabelledTripleAction p q r
      (ramanujanNoncontractingProjector (M+1)
        (ramanujanTripleFourierPhase ((a.val : ℤ),(b.val : ℤ),(c.val : ℤ)))) =
      if p=r ∨ q=r then 0 else ramanujanLabelledTripleAction p q r
        (ramanujanTripleFourierPhase ((a.val : ℤ),(b.val : ℤ),(c.val : ℤ))) := by
  rw [ramanujanNoncontractingProjector_nat_phase M (Finset.mem_Icc.mp a.property).2
    (Finset.mem_Icc.mp b.property).2 (Finset.mem_Icc.mp c.property).2]
  have ha := ramanujanDistinguishedPrimeEntry_band M p a
  have hb := ramanujanDistinguishedPrimeEntry_band M q b
  have hc := ramanujanDistinguishedPrimeEntry_band M r c
  rw [apply_ite (fun F : (ℝ × ℝ × ℝ) → ℂ => ramanujanLabelledTripleAction p q r F)]
  simp only [map_zero,ramanujanLabelledTripleAction_phase,Int.natAbs_natCast,ha,hb,hc]
  by_cases hap : a.val=p.val <;> by_cases hbq : b.val=q.val <;> by_cases hcr : c.val=r.val
  all_goals simp only [hap,hbq,hcr,if_true,if_false,Complex.ofReal_zero,mul_zero,zero_mul,ite_self]
  simp only [Subtype.ext_iff]

/-- Full finite Fourier profiles retain both exclusions, including their intersection. -/
theorem ramanujanLabelledTripleAction_projected_cube (M : ℕ)
    (p q r : RamanujanBandPrime M) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 < n ∧ n ≤ M) (c : ℕ → ℕ → ℕ → ℂ) :
    ramanujanLabelledTripleAction p q r
      (ramanujanNoncontractingProjector (M+1) (ramanujanFiniteCubeTest S c)) =
      if p=r ∨ q=r then 0 else ramanujanLabelledTripleAction p q r (ramanujanFiniteCubeTest S c) := by
  classical
  have he (a b d : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hd : d ∈ S) :=
    ramanujanLabelledTripleAction_projected_phase M p q r
      ⟨a,Finset.mem_Icc.mpr ⟨by have := (hS a ha).1; omega,(hS a ha).2⟩⟩
      ⟨b,Finset.mem_Icc.mpr ⟨by have := (hS b hb).1; omega,(hS b hb).2⟩⟩
      ⟨d,Finset.mem_Icc.mpr ⟨by have := (hS d hd).1; omega,(hS d hd).2⟩⟩
  unfold ramanujanFiniteCubeTest
  simp only [map_sum,map_smul]
  by_cases hm : p=r ∨ q=r
  · simp only [if_pos hm]
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    rw [he a b d ha hb hd,if_pos hm,smul_zero]
  · rw [if_neg hm]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [he a b d ha hb hd,if_neg hm]

/-- Both surviving first-coordinate and second-coordinate label sums omit this label. -/
def ramanujanExcludedLocalGridWeight {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) : ℝ :=
  ∑ p : RamanujanGridPrime P, if p=r then 0 else ramanujanLabelledLocalGridWeight p x

/-- The full complementary product, without replacing any other prime factor. -/
def ramanujanExcludedGridCofactor {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) : ℝ :=
  ∑ p : RamanujanGridPrime P, if p=r then 0 else Real.log p.val *
    ∏ q ∈ (Finset.univ : Finset (RamanujanGridPrime P)).erase r,
      if q.val=p.val then ramanujanGridTag q.val (x q) else ramanujanGridBase q.val (x q)

/-- Each exclusion leaves exactly the base at the third distinguished prime. -/
theorem ramanujanExcludedLocalGridWeight_factor {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) :
    ramanujanExcludedLocalGridWeight r x =
      ramanujanGridBase r.val (x r)*ramanujanExcludedGridCofactor r x := by
  unfold ramanujanExcludedLocalGridWeight ramanujanExcludedGridCofactor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpr : p=r
  · simp only [if_pos hpr,mul_zero]
  · simp only [if_neg hpr,ramanujanLabelledLocalGridWeight]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    rw [if_neg (show r.val ≠ p.val from fun h => hpr (Subtype.ext h.symm))]
    ring

/-- Complete remaining two-coordinate action, after both label exclusions. -/
def ramanujanExcludedLocalPairAction {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) : ℂ :=
  ∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
    (ramanujanExcludedLocalGridWeight r x : ℂ)*(ramanujanExcludedLocalGridWeight r y : ℂ)*
      F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,0)

/-- The full cofactor profile grouped by the two local coordinates of the third prime. -/
def ramanujanExcludedGridProfile {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) (k l : Fin (r.val^2)) : ℂ :=
  ∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
    if x r=k ∧ y r=l then
      (ramanujanExcludedGridCofactor r x : ℂ)*(ramanujanExcludedGridCofactor r y : ℂ)*
        F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,0)
    else 0

private lemma sum_four_comm {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

/-- Exact complete base/base attachment, including both zero coordinates and all cofactors. -/
theorem ramanujanExcludedLocalPairAction_base {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanExcludedLocalPairAction r F =
      ∑ k : Fin (r.val^2), ∑ l : Fin (r.val^2),
        (ramanujanGridBase r.val k : ℂ)*(ramanujanGridBase r.val l : ℂ)*
          ramanujanExcludedGridProfile r F k l := by
  classical
  unfold ramanujanExcludedLocalPairAction ramanujanExcludedGridProfile
  simp only [ramanujanExcludedLocalGridWeight_factor,Complex.ofReal_mul,Finset.mul_sum]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [ite_and,mul_ite,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.sum_const_zero]
  ring

/-- Exact local dephasing; the original full profile is recoverable without approximation. -/
def ramanujanExcludedGridDephasedProfile {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) (k l : Fin (r.val^2)) : ℂ :=
  ramanujanExcludedGridProfile r F k l /
    ramanujanFourierPhase (r.val : ℤ) (((k.val : ℝ)/(r.val^2 : ℕ))*((l.val : ℝ)/(r.val^2 : ℕ)))

/-- The complete signed inverse-profile action, with its full zero fibre retained. -/
def ramanujanExcludedInverseProfileAction {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) : ℂ :=
  let p : Nat.Primes := ⟨r.val,(Finset.mem_filter.mp r.property).2⟩
  let H := fun a b => ramanujanExcludedGridDephasedProfile r F
    (criticalDefectGridNode p a) (criticalDefectGridNode p b)
  ∑ d : ZMod (p : ℕ),
    (if d=0 then criticalProfileAxes p H
      else (r.val : ℂ)⁻¹^2*criticalProfileInverse p H d)*ZMod.stdAddChar d

/-- Full-profile inverse fibres of the literal excluded source, not an isolated local toy. -/
theorem ramanujanExcludedLocalPairAction_inverse {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanExcludedLocalPairAction r F=ramanujanExcludedInverseProfileAction r F := by
  rw [ramanujanExcludedLocalPairAction_base]
  have he := criticalGridBase_profile_pairing
    (⟨r.val,(Finset.mem_filter.mp r.property).2⟩ : Nat.Primes)
    (ramanujanExcludedGridDephasedProfile r F)
  change _ = ramanujanExcludedInverseProfileAction r F at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  unfold ramanujanExcludedGridDephasedProfile
  have hn : ramanujanFourierPhase (r.val : ℤ)
      (((k.val : ℝ)/(r.val^2 : ℕ))*((l.val : ℝ)/(r.val^2 : ℕ))) ≠ 0 := Complex.exp_ne_zero _
  simp only [mul_assoc]
  rw [div_mul_cancel₀ _ hn]

/-- Full third labelled source together with both excluded tangential label sums. -/
def ramanujanExcludedLocalTripleAction {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) : ℂ :=
  ∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
    (ramanujanExcludedLocalGridWeight r x : ℂ)*(ramanujanExcludedLocalGridWeight r y : ℂ)*
      ∑ z : RamanujanLocalGrid P, (ramanujanLabelledLocalGridWeight r z : ℂ)*
        F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,ramanujanLocalGridNode z)

/-- The two exclusion sums keep exactly the same full local tensor. -/
theorem ramanujanExcludedLocalTripleAction_eq {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    (∑ p : RamanujanGridPrime P, ∑ q : RamanujanGridPrime P,
      if p=r ∨ q=r then 0 else ramanujanLabelledTripleAction p q r F) =
      ramanujanExcludedLocalTripleAction r F := by
  classical
  let H (x y : RamanujanLocalGrid P) := ∑ z : RamanujanLocalGrid P,
    (ramanujanLabelledLocalGridWeight r z : ℂ)*
      F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,ramanujanLocalGridNode z)
  have he (p q : RamanujanGridPrime P) :
      (if p=r ∨ q=r then 0 else ramanujanLabelledTripleAction p q r F) =
      ∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
        ((if p=r then 0 else ramanujanLabelledLocalGridWeight p x : ℝ) : ℂ)*
        ((if q=r then 0 else ramanujanLabelledLocalGridWeight q y : ℝ) : ℂ)*H x y := by
    by_cases hp : p=r <;> by_cases hq : q=r
    all_goals simp only [hp,hq,if_true,if_false,true_or,or_true,false_or,
      Complex.ofReal_zero,zero_mul,mul_zero,Finset.sum_const_zero]
    simp only [ramanujanLabelledTripleAction,LinearMap.coe_mk,AddHom.coe_mk,H,
      Finset.mul_sum,mul_assoc]
  simp_rw [he]
  rw [sum_four_comm]
  unfold ramanujanExcludedLocalTripleAction ramanujanExcludedLocalGridWeight
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  change _ = ((∑ p : RamanujanGridPrime P,
    if p=r then 0 else ramanujanLabelledLocalGridWeight p x : ℝ) : ℂ)*
    ((∑ q : RamanujanGridPrime P,
      if q=r then 0 else ramanujanLabelledLocalGridWeight q y : ℝ) : ℂ)*H x y
  generalize H x y = z
  simp only [Complex.ofReal_sum]
  rw [Fintype.sum_mul_sum]
  simp only [Finset.sum_mul]

private lemma sum_three_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- Both original physical projectors transfer to the full excluded local tensor. -/
theorem ramanujanCriticalTripleAtomAction_eq_excludedLocal (M : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 < n ∧ n ≤ M) (c : ℕ → ℕ → ℕ → ℂ) :
    ramanujanCriticalTripleAtomAction (Finset.range (M+1))
      (ramanujanNoncontractingProjector (M+1) (ramanujanFiniteCubeTest S c)) =
      ∑ r : RamanujanBandPrime M, ramanujanExcludedLocalTripleAction r (ramanujanFiniteCubeTest S c) := by
  rw [← ramanujanCompleteLabelledAction_projected_cube M S hS c]
  simp only [ramanujanCompleteLabelledAction,LinearMap.sum_apply,
    ramanujanLabelledTripleAction_projected_cube M _ _ _ S hS c]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro r hr
  exact ramanujanExcludedLocalTripleAction_eq r _

end RHTower.BAGTrace
