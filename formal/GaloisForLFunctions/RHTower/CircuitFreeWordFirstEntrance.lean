import GaloisForLFunctions.RHTower.CircuitCausalAccessibility

/-!
# Free-word reduction of the concurrent causal accessibility

When no two letters commute, the trace monoid is the free monoid: trace equality is word equality
and the causal prefixes of a heap are linearly ordered.  Every successful heap then has exactly one
first successful prefix, the cylinders above the first successful traces are pairwise disjoint, and
the concurrent causal accessibility collapses to the discounted first-entrance mass.

For genuine concurrency this collapse fails: two independent successful letters have a common
extension, so their cylinders overlap.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section FreeWord

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*}

/-- The empty independence relation. -/
def noIndependence (α : Type*) : α → α → Prop := fun _ _ => False

theorem traceEq_noIndependence_iff {u v : List α} :
    TraceEq (noIndependence α) u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => cases hxy with | swap _ _ _ _ hab => exact absurd hab id
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  · rintro rfl
    exact Relation.EqvGen.refl _

theorem traceMk_noIndependence_injective :
    Function.Injective (traceMk (noIndependence α)) := fun _ _ h =>
  traceEq_noIndependence_iff.mp ((traceMk_eq_iff (noIndependence α)).mp h)

theorem traceLen_eq_zero_iff {independent : α → α → Prop} {u : Trace independent} :
    traceLen independent u = 0 ↔ u = 1 := by
  obtain ⟨w, rfl⟩ := traceMk_surjective independent u
  rw [traceLen_traceMk]
  constructor
  · intro h
    rw [List.length_eq_zero_iff.mp h]
    rfl
  · intro h
    have : TraceEq independent w [] := (traceMk_eq_iff independent).mp h
    simpa using (traceEq_perm this).length_eq

/-- In the free monoid the causal prefixes of a heap are linearly ordered. -/
theorem tracePrefix_noIndependence_total {u v T : Trace (noIndependence α)}
    (hu : TracePrefix (noIndependence α) u T) (hv : TracePrefix (noIndependence α) v T) :
    TracePrefix (noIndependence α) u v ∨ TracePrefix (noIndependence α) v u := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  obtain ⟨u', rfl⟩ := traceMk_surjective (noIndependence α) u
  obtain ⟨v', rfl⟩ := traceMk_surjective (noIndependence α) v
  obtain ⟨a', rfl⟩ := traceMk_surjective (noIndependence α) a
  obtain ⟨b', rfl⟩ := traceMk_surjective (noIndependence α) b
  obtain ⟨T', rfl⟩ := traceMk_surjective (noIndependence α) T
  rw [traceMk_mul] at ha hb
  have ha' : T' = u' ++ a' := traceMk_noIndependence_injective ha
  have hb' : T' = v' ++ b' := traceMk_noIndependence_injective hb
  have hpu : u' <+: T' := ⟨a', ha'.symm⟩
  have hpv : v' <+: T' := ⟨b', hb'.symm⟩
  rcases List.prefix_or_prefix_of_prefix hpu hpv with h | h
  · obtain ⟨c, hc⟩ := h
    exact Or.inl ⟨traceMk (noIndependence α) c, by rw [traceMk_mul, ← hc]⟩
  · obtain ⟨c, hc⟩ := h
    exact Or.inr ⟨traceMk (noIndependence α) c, by rw [traceMk_mul, ← hc]⟩

theorem eq_of_tracePrefix_of_traceLen_le {independent : α → α → Prop} {u v : Trace independent}
    (h : TracePrefix independent u v) (hlen : traceLen independent v ≤ traceLen independent u) :
    u = v := by
  obtain ⟨w, rfl⟩ := h
  have hw : traceLen independent w = 0 := by
    rw [traceLen_mul] at hlen
    omega
  rw [traceLen_eq_zero_iff.mp hw, mul_one]

/-- The first successful causal prefixes of a target dictionary. -/
def firstSuccessfulTrace (independent : α → α → Prop) (S : Trace independent → Set X) (x : X) :
    Set (Trace independent) :=
  {u | x ∈ S u ∧ ∀ v, TracePrefix independent v u → x ∈ S v → v = u}

/-- Every successful heap has a first successful causal prefix. -/
theorem exists_firstSuccessful_prefix (independent : α → α → Prop)
    (S : Trace independent → Set X) (x : X) {T : Trace independent}
    (hT : T ∈ causalSuccessEvent independent S x) :
    ∃ u ∈ firstSuccessfulTrace independent S x, TracePrefix independent u T := by
  classical
  obtain ⟨u₀, hu₀, hxu₀⟩ := hT
  set F : Finset (Trace independent) :=
    ((tracePrefixSet_finite independent T).toFinset).filter fun u => x ∈ S u with hFdef
  have hu₀F : u₀ ∈ F := by
    rw [hFdef, Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset (tracePrefixSet_finite independent T)).mpr hu₀, hxu₀⟩
  obtain ⟨u, huF, hmin⟩ := F.exists_min_image (traceLen independent) ⟨u₀, hu₀F⟩
  rw [hFdef, Finset.mem_filter] at huF
  have huT : TracePrefix independent u T :=
    (Set.Finite.mem_toFinset (tracePrefixSet_finite independent T)).mp huF.1
  refine ⟨u, ⟨huF.2, ?_⟩, huT⟩
  intro v hvu hxv
  have hvT : TracePrefix independent v T := by
    obtain ⟨w, rfl⟩ := hvu
    obtain ⟨w', rfl⟩ := huT
    exact ⟨w * w', by rw [mul_assoc]⟩
  have hvF : v ∈ F := by
    rw [hFdef, Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset (tracePrefixSet_finite independent T)).mpr hvT, hxv⟩
  exact eq_of_tracePrefix_of_traceLen_le hvu (hmin v hvF)

/-- In the free monoid the first successful causal prefix of a heap is unique. -/
theorem firstSuccessful_unique (S : Trace (noIndependence α) → Set X) (x : X)
    {T u v : Trace (noIndependence α)}
    (hu : u ∈ firstSuccessfulTrace (noIndependence α) S x)
    (hv : v ∈ firstSuccessfulTrace (noIndependence α) S x)
    (huT : TracePrefix (noIndependence α) u T) (hvT : TracePrefix (noIndependence α) v T) :
    u = v := by
  rcases tracePrefix_noIndependence_total huT hvT with h | h
  · exact hv.2 u h hu.1
  · exact (hu.2 v h hv.1).symm

theorem incidentEdgeCount_le_card (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (a : α) :
    incidentEdgeCount independent a ≤ Fintype.card α := by
  have h := incidentEdgeCount_succ_le_of_dependentSubset independent hsymm a
    (Finset.univ : Finset α) (fun b _ _ => Finset.mem_univ b) (Finset.mem_univ a)
  rw [Finset.card_univ] at h
  omega

/-- **Free-word first-entrance reduction.**  With no independent letters, the concurrent causal
accessibility collapses to the discounted first-entrance mass over the first successful traces. -/
theorem causalAccessibility_noIndependence_eq (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount (noIndependence α) a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    (S : Trace (noIndependence α) → Set X) (x : X) :
    causalAccessibility (noIndependence α) z S x =
      ∑' u : firstSuccessfulTrace (noIndependence α) S x,
        z ^ traceLen (noIndependence α) (u : Trace (noIndependence α)) := by
  classical
  set ind : α → α → Prop := noIndependence α with hind
  have hsymm : ∀ x y : α, ind x y → ind y x := fun _ _ h => h
  have hZpos := tracePartition_pos ind hsymm Δ hdegree hz0 hz
  have hsumz := summable_tracePow ind hsymm Δ hdegree hz0 hz
  set w : Trace ind → ℝ := fun T => z ^ traceLen ind T with hwdef
  have hpt : ∀ T : Trace ind,
      Set.indicator (causalSuccessEvent ind S x) (fun T => ENNReal.ofReal (w T)) T =
        ∑' u : firstSuccessfulTrace ind S x,
          Set.indicator (traceCylinder ind (u : Trace ind))
            (fun T => ENNReal.ofReal (w T)) T := by
    intro T
    by_cases hT : T ∈ causalSuccessEvent ind S x
    · obtain ⟨u₀, hu₀, hu₀T⟩ := exists_firstSuccessful_prefix ind S x hT
      rw [Set.indicator_of_mem hT]
      rw [tsum_eq_single (⟨u₀, hu₀⟩ : firstSuccessfulTrace ind S x) ?_]
      · rw [Set.indicator_of_mem (show T ∈ traceCylinder ind u₀ from hu₀T)]
      · rintro ⟨v, hv⟩ hne
        refine Set.indicator_of_notMem (fun hcon => hne ?_) _
        exact Subtype.ext (firstSuccessful_unique S x hv hu₀ hcon hu₀T)
    · rw [Set.indicator_of_notMem hT]
      refine (tsum_eq_zero_iff ENNReal.summable).mpr ?_
      rintro ⟨v, hv⟩
      refine Set.indicator_of_notMem (fun hcon => hT ?_) _
      exact ⟨v, hcon, hv.1⟩
  have hswap : (∑' T : Trace ind,
      Set.indicator (causalSuccessEvent ind S x) (fun T => ENNReal.ofReal (w T)) T) =
      ∑' u : firstSuccessfulTrace ind S x,
        ENNReal.ofReal (w (u : Trace ind)) * tracePartitionENN ind z := by
    simp_rw [hpt]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun u => ?_
    rw [← tsum_subtype (traceCylinder ind (u : Trace ind))
      (fun T : Trace ind => ENNReal.ofReal (w T))]
    exact tsum_traceCylinderENN ind hsymm hz0 (u : Trace ind)
  have hleft : (∑' T : Trace ind,
      Set.indicator (causalSuccessEvent ind S x) (fun T => ENNReal.ofReal (w T)) T) =
      ENNReal.ofReal (∑' T : causalSuccessEvent ind S x, w (T : Trace ind)) := by
    rw [tsum_subtype (causalSuccessEvent ind S x) w,
      ENNReal.ofReal_tsum_of_nonneg
        (fun T => by
          by_cases h : T ∈ causalSuccessEvent ind S x <;>
            simp [Set.indicator, h, hwdef, pow_nonneg hz0])
        (hsumz.indicator (causalSuccessEvent ind S x))]
    refine tsum_congr fun T => ?_
    by_cases hT : T ∈ causalSuccessEvent ind S x
    · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT]
    · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT, ENNReal.ofReal_zero]
  have hright : (∑' u : firstSuccessfulTrace ind S x,
      ENNReal.ofReal (w (u : Trace ind)) * tracePartitionENN ind z) =
      ENNReal.ofReal ((∑' u : firstSuccessfulTrace ind S x, w (u : Trace ind)) *
        tracePartition ind z) := by
    rw [ENNReal.tsum_mul_right, tracePartitionENN_eq_ofReal ind hsymm Δ hdegree hz0 hz,
      ← ENNReal.ofReal_mul (tsum_nonneg fun u => by positivity)]
    congr 1
    congr 1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun u => by positivity)
      (hsumz.subtype (fun v => v ∈ firstSuccessfulTrace ind S x))]
  have hEq : ENNReal.ofReal (∑' T : causalSuccessEvent ind S x, w (T : Trace ind)) =
      ENNReal.ofReal ((∑' u : firstSuccessfulTrace ind S x, w (u : Trace ind)) *
        tracePartition ind z) := by
    rw [← hleft, hswap, hright]
  have hreal : (∑' T : causalSuccessEvent ind S x, w (T : Trace ind)) =
      (∑' u : firstSuccessfulTrace ind S x, w (u : Trace ind)) * tracePartition ind z := by
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp hEq
    · exact tsum_nonneg fun T => by positivity
    · exact mul_nonneg (tsum_nonneg fun u => by positivity) hZpos.le
  rw [causalAccessibility, traceMass, hreal, mul_div_assoc, div_self (ne_of_gt hZpos), mul_one]

end FreeWord

end GaloisForLFunctions.RHTower
