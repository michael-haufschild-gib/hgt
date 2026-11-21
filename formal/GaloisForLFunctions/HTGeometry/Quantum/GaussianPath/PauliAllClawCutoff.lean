import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliClawExtrema
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliClawWitnessLocality
import Mathlib.Data.Finset.Powerset

/-!
# Upper Gaussian cutoff for all Pauli claws with distinguishable leaves

Every such claw uses six distinct terms in a five-row window. A union
bound over the six-element subsets of the window gives the same
logarithmic upper scale as the explicit six-coordinate certificate.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev FiveRowIndex := Fin 5 × PathPauliDirections

private def fiveRows (k : ℕ) (ω : PathPauliDisorder) (i : FiveRowIndex) : ℝ :=
  ω (k + i.1.val, i.2)

private theorem measurePreserving_fiveRows (k : ℕ) :
    MeasurePreserving (fiveRows k) pathPauliDisorderLaw
      (Measure.infinitePi fun _ : FiveRowIndex => gaussianReal 0 1) := by
  let f (i : FiveRowIndex) : ℕ × PathPauliDirections := (k + i.1.val, i.2)
  have hf : Function.Injective f := by
    rintro ⟨i, d⟩ ⟨j, e⟩ h
    obtain ⟨hr, hd⟩ := Prod.mk.inj h
    exact Prod.ext (Fin.ext (Nat.add_left_cancel hr)) hd
  exact ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _),
    Measure.map_infinitePi_infinitePi_of_inj hf⟩

private def largeCoordinates (t : ℝ) (I : Finset FiveRowIndex) : Set (FiveRowIndex → ℝ) :=
  (I : Set FiveRowIndex).pi (fun _ => {x : ℝ | t < |x|})

private theorem measurableSet_absoluteTail' (t : ℝ) : MeasurableSet {x : ℝ | t < |x|} :=
  measurableSet_lt measurable_const measurable_id.abs

private theorem measure_largeCoordinates (k : ℕ) (t : ℝ) (I : Finset FiveRowIndex) :
    pathPauliDisorderLaw ((fiveRows k) ⁻¹' largeCoordinates t I) =
      gaussianAbsoluteTailMass t ^ I.card := by
  have hm := measurePreserving_fiveRows k
  have hI : MeasurableSet (largeCoordinates t I) :=
    MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_absoluteTail' t)
  rw [← Measure.map_apply hm.measurable hI, hm.map_eq, largeCoordinates,
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_absoluteTail' t),
    Finset.prod_const, gaussianAbsoluteTailMass]
  rfl

/-- Some five-row window starting in the prefix has six coordinates above the cutoff. -/
def sixInFiveRows (n : ℕ) (t : ℝ) : Set PathPauliDisorder :=
  ⋃ k ∈ Finset.range (n + 2), ⋃ I ∈ Finset.powersetCard 6 (Finset.univ : Finset FiveRowIndex),
    (fiveRows k) ⁻¹' largeCoordinates t I

private theorem mem_sixInFiveRows_iff (ω : PathPauliDisorder) (n : ℕ) (t : ℝ) :
    ω ∈ sixInFiveRows n t ↔
      ∃ k < n + 2, ∃ I : Finset FiveRowIndex, I.card = 6 ∧
        ∀ i ∈ I, t < |fiveRows k ω i| := by
  simp [sixInFiveRows, largeCoordinates, Set.mem_iUnion, Finset.mem_powersetCard,
    Finset.subset_univ, exists_prop]

/-- Adding window starts preserves a six-coordinate exceedance. -/
theorem sixInFiveRows_mono (t : ℝ) : Monotone (fun n => sixInFiveRows n t) := by
  intro n m h ω hw
  obtain ⟨k, hk, I, hI, hi⟩ := (mem_sixInFiveRows_iff ω n t).mp hw
  exact (mem_sixInFiveRows_iff ω m t).mpr
    ⟨k, hk.trans_le (Nat.add_le_add_right h _), I, hI, hi⟩

/-- Increasing the threshold can only remove exceedances. -/
theorem sixInFiveRows_antitone (n : ℕ) : Antitone (sixInFiveRows n) := by
  intro t u h ω hw
  obtain ⟨k, hk, I, hI, hi⟩ := (mem_sixInFiveRows_iff ω n u).mp hw
  exact (mem_sixInFiveRows_iff ω n t).mpr
    ⟨k, hk, I, hI, fun i hi' => h.trans_lt (hi i hi')⟩

private theorem card_fiveRowIndex : Fintype.card FiveRowIndex = 60 := by
  simp [FiveRowIndex, PathPauliDirections, Fintype.card_prod, Fintype.card_sum]

/-- Union bound over window starts and six-element subsets of their coordinates. -/
theorem gaussian_measure_sixInFiveRows_le (n : ℕ) (t : ℝ) :
    pathPauliDisorderLaw (sixInFiveRows n t) ≤
      ((n + 2 : ℕ) : ENNReal) * (Nat.choose 60 6 : ENNReal) * gaussianAbsoluteTailMass t ^ 6 := by
  let C := Finset.powersetCard 6 (Finset.univ : Finset FiveRowIndex)
  have hc : C.card = Nat.choose 60 6 := by
    rw [show C = Finset.powersetCard 6 Finset.univ from rfl,
      Finset.card_powersetCard, Finset.card_univ, card_fiveRowIndex]
  let E (k : ℕ) := ⋃ I ∈ C, (fiveRows k) ⁻¹' largeCoordinates t I
  have hrow (k : ℕ) : pathPauliDisorderLaw (E k) ≤
      (Nat.choose 60 6 : ENNReal) * gaussianAbsoluteTailMass t ^ 6 := by
    apply (measure_biUnion_finset_le _ _).trans_eq
    calc
      _ = ∑ _ ∈ C, gaussianAbsoluteTailMass t ^ 6 := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [measure_largeCoordinates, (Finset.mem_powersetCard.mp hI).2]
      _ = _ := by rw [Finset.sum_const, hc, nsmul_eq_mul]
  change pathPauliDisorderLaw (⋃ k ∈ Finset.range (n + 2), E k) ≤ _
  refine (measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum (fun k _ => hrow k)).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

variable {n : ℕ}

private theorem pathPauliSourceCoordinate_injective :
    Function.Injective (@pathPauliSourceCoordinate n) := by
  rintro (⟨i, a⟩ | ⟨i, a⟩) (⟨j, b⟩ | ⟨j, b⟩) h <;>
    simp [pathPauliSourceCoordinate, Fin.ext_iff] at h ⊢ <;> exact h

private theorem pathPauliRow_lt (l : PathLabel n) : pathPauliRow l < n + 2 := by
  rcases l with ⟨i, a⟩ | ⟨e, ab⟩
  · exact i.isLt
  · exact e.isLt.trans (Nat.lt_succ_self _)

/-- An induced Pauli claw whose leaves have distinct neighborhoods. -/
structure DistinguishedPathClaw (S : Set (PathLabel n)) where
  center : S
  leafA : S
  leafB : S
  leafC : S
  centerA : pathFrustrationAdj S center leafA
  centerB : pathFrustrationAdj S center leafB
  centerC : pathFrustrationAdj S center leafC
  independentAB : ¬pathFrustrationAdj S leafA leafB
  independentAC : ¬pathFrustrationAdj S leafA leafC
  independentBC : ¬pathFrustrationAdj S leafB leafC
  distinguishAB : ∃ w, ¬(pathFrustrationAdj S leafA w ↔ pathFrustrationAdj S leafB w)
  distinguishAC : ∃ w, ¬(pathFrustrationAdj S leafA w ↔ pathFrustrationAdj S leafC w)
  distinguishBC : ∃ w, ¬(pathFrustrationAdj S leafB w ↔ pathFrustrationAdj S leafC w)

/-- A distinguished claw on above-cutoff terms forces a six-coordinate window hit. -/
theorem DistinguishedPathClaw.mem_sixInFiveRows {S : Set (PathLabel n)} (C : DistinguishedPathClaw S)
    (ω : PathPauliDisorder) (t : ℝ)
    (hS : ∀ l ∈ S, t < |pathPauliDisorderShell ω n l|) :
    ω ∈ sixInFiveRows n t := by
  obtain ⟨F, hFcard, hFS, hnear⟩ := exists_six_local_terms_of_distinguished_claw S
    C.center C.leafA C.leafB C.leafC C.centerA C.centerB C.centerC
    C.independentAB C.independentAC C.independentBC C.distinguishAB C.distinguishAC C.distinguishBC
  let k := pathPauliRow C.center.1 - 2
  have hk : k < n + 2 := (Nat.sub_le _ _).trans_lt (pathPauliRow_lt C.center.1)
  have hlow (l : F) : k ≤ pathPauliRow l.1 := by
    have h := (hnear l.1 l.2).2
    dsimp [k]
    omega
  have hhigh (l : F) : pathPauliRow l.1 - k < 5 := by
    have h := (hnear l.1 l.2).1
    dsimp [k]
    omega
  let f (l : F) : FiveRowIndex :=
    (⟨pathPauliRow l.1 - k, hhigh l⟩, (pathPauliSourceCoordinate l.1).2)
  have hf : Function.Injective f := by
    intro u v he
    obtain ⟨hrow, hd⟩ := Prod.mk.inj he
    have hr : pathPauliRow u.1 - k = pathPauliRow v.1 - k := congrArg Fin.val hrow
    apply Subtype.ext
    apply pathPauliSourceCoordinate_injective
    apply Prod.ext _ hd
    change pathPauliRow u.1 = pathPauliRow v.1
    have hu := hlow u
    have hv := hlow v
    omega
  let I := F.attach.map ⟨f, hf⟩
  refine (mem_sixInFiveRows_iff ω n t).mpr ⟨k, hk, I, ?_, ?_⟩
  · simpa only [I, Finset.card_map, Finset.card_attach] using hFcard
  · intro i hi
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hi
    change t < |ω (k + (pathPauliRow l.1 - k), (pathPauliSourceCoordinate l.1).2)|
    rw [Nat.add_sub_of_le (hlow l)]
    change t < |ω (pathPauliSourceCoordinate l.1)|
    rw [← pathPauliDisorderShell_apply_source ω l.1]
    exact hS l.1 (hFS l.1 l.2)

/-- Finite bound uniform over every support consisting of above-cutoff coefficients. -/
theorem gaussian_measure_exists_distinguishedClaw_le (n : ℕ) (t : ℝ) :
    pathPauliDisorderLaw {ω | ∃ S : Set (PathLabel n),
      (∀ l ∈ S, t < |pathPauliDisorderShell ω n l|) ∧ Nonempty (DistinguishedPathClaw S)} ≤
      ((n + 2 : ℕ) : ENNReal) * (Nat.choose 60 6 : ENNReal) * gaussianAbsoluteTailMass t ^ 6 := by
  refine (measure_mono ?_).trans (gaussian_measure_sixInFiveRows_le n t)
  rintro ω ⟨S, hS, ⟨C⟩⟩
  exact C.mem_sixInFiveRows ω t hS

private theorem sixInFiveRows_exp_bound (n : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    pathPauliDisorderLaw (sixInFiveRows n (clawCutoffScale n + η)) ≤
      ENNReal.ofReal ((128 * Nat.choose 60 6 : ℝ) * Real.exp (-(6 * η * clawCutoffScale n))) := by
  let r := clawCutoffScale n
  let N := (n : ℝ) + 1
  let t := r + η
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 ≤ t := add_nonneg (Real.sqrt_nonneg _) hη
  have hlog : Real.log N = 3 * r ^ 2 := by
    have hr : r ^ 2 = Real.log N / 3 := clawCutoffScale_sq n
    linarith only [hr]
  have he : Real.exp (-(3 * t ^ 2)) ≤ Real.exp (-(6 * η * r)) / N := by
    rw [← Real.exp_log hN, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    rw [hlog]
    dsimp [t]
    nlinarith only [sq_nonneg η]
  have hsix : (2 * Real.exp (-(t ^ 2 / 2))) ^ 6 = 64 * Real.exp (-(3 * t ^ 2)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have hc : ((6 : ℕ) : ℝ) * -(t ^ 2 / 2) = -(3 * t ^ 2) := by push_cast; ring
    rw [hc]
    norm_num
  refine (gaussian_measure_sixInFiveRows_le n t).trans ?_
  calc
    _ ≤ ((n + 2 : ℕ) : ENNReal) * (Nat.choose 60 6 : ENNReal) *
        ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2))) ^ 6 :=
      mul_le_mul_right (pow_le_pow_left' (gaussianAbsoluteTailMass_exp_upper ht) 6) _
    _ = ENNReal.ofReal (((n + 2 : ℕ) : ℝ) * (Nat.choose 60 6 : ℝ) *
        (2 * Real.exp (-(t ^ 2 / 2))) ^ 6) := by
      have hp : 0 ≤ ((n + 2 : ℕ) : ℝ) * (Nat.choose 60 6 : ℝ) := by positivity
      rw [ENNReal.ofReal_mul hp, ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) (n + 2)),
        ENNReal.ofReal_pow (by positivity)]
      simp only [ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [hsix]
      have h2 : ((n + 2 : ℕ) : ℝ) ≤ 2 * N := by dsimp [N]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ (2 * N) * (Nat.choose 60 6 : ℝ) * (64 * (Real.exp (-(6 * η * r)) / N)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2 (by positivity))
            (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity) (by positivity)
        _ = _ := by field_simp [hN.ne']; ring

/-- Almost surely, every positive margin above the scale eventually
rules out every distinguished claw on retained above-cutoff terms. -/
theorem gaussian_ae_eventually_no_distinguishedClaw_above {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ S : Set (PathLabel n),
        (∀ l ∈ S, clawCutoffScale n + ε < |pathPauliDisorderShell ω n l|) →
        IsEmpty (DistinguishedPathClaw S) := by
  filter_upwards [gaussian_ae_eventually_notMem_prefixEvents_above sixInFiveRows
    sixInFiveRows_mono sixInFiveRows_antitone
      (by positivity) hε sixInFiveRows_exp_bound] with ω hω
  filter_upwards [hω] with n hn S hS
  exact ⟨fun C => hn (C.mem_sixInFiveRows ω _ hS)⟩

/-- One probability-one event works simultaneously for every fixed positive margin. -/
theorem gaussian_ae_eventually_no_distinguishedClaw_above_all_margins :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ S : Set (PathLabel n),
        (∀ l ∈ S, clawCutoffScale n + ε < |pathPauliDisorderShell ω n l|) →
        IsEmpty (DistinguishedPathClaw S) := by
  have h (k : ℕ) := gaussian_ae_eventually_no_distinguishedClaw_above
    (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hle : 1 / ((k : ℝ) + 1) ≤ ε := by
    have he := (div_lt_iff₀ hε).mp hk
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith only [he, hε]
  filter_upwards [hω k] with n hn S hS
  have ht : clawCutoffScale n + 1 / ((k : ℝ) + 1) ≤ clawCutoffScale n + ε := by
    linarith only [hle]
  exact hn S fun l hl => ht.trans_lt (hS l hl)

#print axioms gaussian_measure_sixInFiveRows_le
#print axioms gaussian_measure_exists_distinguishedClaw_le
#print axioms gaussian_ae_eventually_no_distinguishedClaw_above_all_margins

end

end GaloisForLFunctions.HTGeometry
