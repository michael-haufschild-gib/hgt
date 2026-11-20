import GaloisForLFunctions.ExceptionalLayerTheory.ArbitraryDerivativeOrdersSeparateTheMultiplicityCounts
import Mathlib.Data.Finset.Sort

/-!
# One high derivative area identifies the entire multiplicity histogram

Two different real histograms on W positive multiplicities agree at
fewer than W distinct derivative orders. With integer coefficients
bounded by the winding, only finitely many histogram pairs exist.
Consequently every sufficiently high derivative order separates them
all. At each such order the nearest predicted area eventually gives the
exact histogram of the disk, using one scalar observation.
-/

noncomputable section
open Complex Filter Set Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A pair of distinct histograms can agree on at most W−1 orders. -/
theorem derivative_area_collision_bound {W : ℕ} {a b : Fin W → ℝ} (hab : a≠b)
    (s : Finset ℕ) (hs : ∀ j ∈ s, divisorAreaMoment j a=divisorAreaMoment j b) : s.card<W := by
  by_contra! h
  obtain ⟨t,ht,hcard⟩ := Finset.exists_subset_card_eq h
  let d := t.orderEmbOfFin hcard
  exact hab (divisor_area_moments_injective d.strictMono (funext fun i =>
    hs (d i) (ht (t.orderEmbOfFin_mem hcard i))))

private theorem finitely_many_collisions {W : ℕ} {a b : Fin W → ℝ} (hab : a≠b) :
    {j : ℕ | divisorAreaMoment j a=divisorAreaMoment j b}.Finite := by
  by_contra hinf
  obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hinf W
  exact (derivative_area_collision_bound hab s (fun j hj => hs hj)).ne hcard

/-- Integer multiplicity counts bounded in each coordinate by W. -/
abbrev BoundedOrderCounts (W : ℕ) := Fin W → Fin (W+1)

def boundedOrderMoment {W : ℕ} (j : ℕ) (a : BoundedOrderCounts W) :=
  divisorAreaMoment j (fun k => (a k).val)

/-- The derivative order threshold depends on W alone. Beyond it, one
real area separates all integer histograms with this bound. -/
theorem high_orders_separate_all_bounded_counts (W : ℕ) :
    ∀ᶠ j : ℕ in atTop, Function.Injective (boundedOrderMoment (W:=W) j) := by
  classical
  have hpair (a b : BoundedOrderCounts W) :
      ∀ᶠ j : ℕ in atTop, boundedOrderMoment j a=boundedOrderMoment j b → a=b := by
    by_cases hab : a=b
    · exact Eventually.of_forall fun _ _ => hab
    · have hreal : (fun k => ((a k).val:ℝ))≠(fun k => ((b k).val:ℝ)) := by
        intro he
        apply hab
        funext k
        apply Fin.ext
        exact_mod_cast congrFun he k
      obtain ⟨B,hB⟩ := (finitely_many_collisions hreal).bddAbove
      filter_upwards [eventually_gt_atTop B] with j hj
      exact fun he => (hj.not_ge (hB he)).elim
  have h := eventually_all.mpr (fun a => eventually_all.mpr (hpair a))
  exact h.mono fun _ hj a b => hj a b

/-- A measurement converging to one of finitely many distinct values
eventually has that value as its unique nearest candidate. -/
theorem nearest_finite_observation {α : Type*} [Finite α] {v : α → ℝ} (hv : Function.Injective v)
    {F : ℝ → ℝ} {a : α} (hF : Tendsto F atTop (𝓝 (v a))) :
    ∀ᶠ u : ℝ in atTop, ∀ b : α,
      (∀ d : α, |F u-v b|≤|F u-v d|) ↔ b=a := by
  classical
  have hsep (b : α) : ∀ᶠ u : ℝ in atTop, b≠a → |F u-v a| < |F u-v b| := by
    by_cases he : b=a
    · exact Eventually.of_forall fun _ hn => (hn he).elim
    · have hdist : |v a-v a| < |v a-v b| := by
        rw [sub_self,abs_zero]
        exact abs_pos.mpr (sub_ne_zero.mpr (hv.ne (Ne.symm he)))
      exact ((hF.sub_const (v a)).abs.eventually_lt (hF.sub_const (v b)).abs hdist).mono fun _ h _ => h
  filter_upwards [eventually_all.mpr hsep] with u hu
  intro b
  constructor
  · intro hm
    by_contra he
    exact (hu b he).not_ge (hm a)
  · intro hba d
    rw [hba]
    by_cases he : d=a
    · rw [he]
    · exact (hu d he).le

/-- For every sufficiently high derivative order, a single measured
area has the true histogram as its unique nearest bounded integer
prediction at all sufficiently high thresholds. -/
theorem one_derivative_area_decodes_the_xi_divisor (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      ∀ᶠ j : ℕ in atTop, ∀ᶠ u : ℝ in atTop, ∀ b : BoundedOrderCounts W,
        (∀ d : BoundedOrderCounts W,
          |xiDerivativeDiskArea j c R u-boundedOrderMoment j b| ≤
            |xiDerivativeDiskArea j c R u-boundedOrderMoment j d|) ↔
          ∀ k, (b k).val=divisorOrderCounts t W k := by
  dsimp only
  let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
  obtain ⟨t,ht,hcap,ha⟩ := xi_disk_bounded_order_counts c hR hb
  let a : BoundedOrderCounts W := fun k => ⟨divisorOrderCounts t W k,Nat.lt_succ_of_le (hcap k)⟩
  refine ⟨t,ht,?_⟩
  filter_upwards [high_orders_separate_all_bounded_counts W] with j hj
  have hl : Tendsto (xiDerivativeDiskArea j c R) atTop (𝓝 (boundedOrderMoment j a)) := ha j
  filter_upwards [nearest_finite_observation hj hl] with u hu
  intro b
  rw [hu]
  exact ⟨fun he k => congrArg Fin.val (congrFun he k),fun he => funext fun k => Fin.ext (he k)⟩

#print axioms derivative_area_collision_bound
#print axioms high_orders_separate_all_bounded_counts
#print axioms one_derivative_area_decodes_the_xi_divisor
end GaloisForLFunctions.ExceptionalLayerTheory
