import GaloisForLFunctions.HTGeometry.CompactTailDenseConstraintKernel

/-!
# Tail-dense tensor separation by an asymptotic scale

This file proves a general separation law. A finite family of continuous observables on a
tail-dense constraint space remains independent after tensoring with any finite asymptotic scale.
The coefficient geometry and the external clock cannot conspire: at every constraint point, the
dominant scale is isolated on the cluster pullback filter, and induction removes the remaining
scales.

Prime Dirichlet shifts and logarithmic jet powers form the principal arithmetic application, but
the theorem is independent of that realization.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- A finite-coordinate asymptotic scale modulo finite support. Every nonempty finite subfamily
has a nowhere-zero dominant weight relative to which all other weights tend to zero. -/
def CofiniteAsymptoticScale {I P : Type*} (w : I → P → ℂ) : Prop :=
  (∀ i p, w i p ≠ 0) ∧
    ∀ s : Finset I, s.Nonempty →
      ∃ i₀ ∈ s, ∀ i ∈ s, i ≠ i₀ →
        Tendsto (fun p => w i p / w i₀ p) cofinite (𝓝 0)

/-- Pull the neighbourhood filter of one constraint point back to the coordinate set and retain
the cofinite tail. -/
def clusterPullbackFilter {P V : Type*} [TopologicalSpace V]
    (x : P → V) (v : V) : Filter P :=
  comap x (𝓝 v) ⊓ cofinite

/-- A tail cluster point makes its pullback filter nontrivial. -/
theorem clusterPullbackFilter_neBot
    {P V : Type*} [TopologicalSpace V]
    {x : P → V} {v : V} (hv : MapClusterPt v cofinite x) :
    NeBot (clusterPullbackFilter x v) := by
  exact (neBot_inf_comap_iff_map').2 hv.clusterPt

/-- The profile converges to the selected constraint point on its cluster pullback filter. -/
theorem tendsto_clusterPullbackFilter
    {P V : Type*} [TopologicalSpace V] (x : P → V) (v : V) :
    Tendsto x (clusterPullbackFilter x v) (𝓝 v) := by
  exact tendsto_iff_comap.mpr inf_le_left

/-- Every cofinite limit remains valid after localization at a tail cluster point. -/
theorem tendsto_clusterPullbackFilter_of_cofinite
    {P V Y : Type*} [TopologicalSpace V] [TopologicalSpace Y]
    (x : P → V) (v : V) {g : P → Y} {y : Y}
    (hg : Tendsto g cofinite (𝓝 y)) :
    Tendsto g (clusterPullbackFilter x v) (𝓝 y) :=
  hg.mono_left inf_le_right

private theorem asymptoticScale_coefficients_zero_on_finset
    {P V I J : Type*} [TopologicalSpace V] [Fintype J]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (w : I → P → ℂ) (hw : CofiniteAsymptoticScale w) :
    ∀ s : Finset I, ∀ c : J → I → ℂ,
      (∀ᶠ p in cofinite,
        ∑ i ∈ s, (∑ j, c j i * f j (x p)) * w i p = 0) →
      ∀ i ∈ s, ∀ j, c j i = 0 := by
  classical
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      intro c hrelation
      rcases s.eq_empty_or_nonempty with hsempty | hsnonempty
      · simp [hsempty]
      obtain ⟨i₀, hi₀, hdominates⟩ := hw.2 s hsnonempty
      let g : I → V → ℂ := fun i v => ∑ j, c j i * f j v
      have hg : ∀ i, Continuous (g i) := by
        intro i
        dsimp only [g]
        fun_prop
      have hgi₀ : ∀ v ∈ K, g i₀ v = 0 := by
        intro v hv
        let G : Filter P := clusterPullbackFilter x v
        haveI : NeBot G := clusterPullbackFilter_neBot (hx.2 v hv)
        have hxv : Tendsto x G (𝓝 v) := tendsto_clusterPullbackFilter x v
        have hterm : ∀ i ∈ s,
            Tendsto (fun p => g i (x p) * (w i p / w i₀ p)) G
              (𝓝 (if i = i₀ then g i₀ v else 0)) := by
          intro i hi
          by_cases hii₀ : i = i₀
          · subst i
            simpa [hw.1] using! (hg i₀).tendsto v |>.comp hxv
          · have hratio := tendsto_clusterPullbackFilter_of_cofinite x v
                (hdominates i hi hii₀)
            have hcoeff := (hg i).tendsto v |>.comp hxv
            simpa [hii₀] using hcoeff.mul hratio
        have hsum : Tendsto
            (fun p => ∑ i ∈ s, g i (x p) * (w i p / w i₀ p)) G
            (𝓝 (g i₀ v)) := by
          have ht := tendsto_finsetSum s hterm
          have htarget : (∑ i ∈ s, if i = i₀ then g i₀ v else 0) = g i₀ v := by
            rw [Finset.sum_eq_single i₀]
            · simp
            · intro b hb hbi₀
              simp [hbi₀]
            · exact fun hnot => (hnot hi₀).elim
          simpa [htarget] using ht
        have hrelationG : ∀ᶠ p in G,
            ∑ i ∈ s, g i (x p) * (w i p / w i₀ p) = 0 := by
          filter_upwards [hrelation.filter_mono inf_le_right] with p hp
          have hrewrite :
              (∑ i ∈ s, g i (x p) * (w i p / w i₀ p)) =
                (∑ i ∈ s, g i (x p) * w i p) / w i₀ p := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [hrewrite]
          have hp' : (∑ i ∈ s, g i (x p) * w i p) = 0 := by
            simpa only [g] using hp
          rw [hp', zero_div]
        have hzero : Tendsto
            (fun p => ∑ i ∈ s, g i (x p) * (w i p / w i₀ p)) G
            (𝓝 0) :=
          tendsto_const_nhds.congr' (hrelationG.mono fun _ hp => hp.symm)
        exact tendsto_nhds_unique hsum hzero
      have hc₀ : ∀ j, c j i₀ = 0 := by
        rw [Fintype.linearIndependent_iff] at hlinear
        have hsum : (∑ j, c j i₀ • (fun v : K => f j v.1)) = 0 := by
          funext v
          simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g] using hgi₀ v.1 v.2
        exact hlinear (fun j => c j i₀) hsum
      have hrelationErase : ∀ᶠ p in cofinite,
          ∑ i ∈ s.erase i₀, (∑ j, c j i * f j (x p)) * w i p = 0 := by
        filter_upwards [hrelation] with p hp
        have hsplit := Finset.add_sum_erase s
          (fun i => (∑ j, c j i * f j (x p)) * w i p) hi₀
        have hi₀zero : (∑ j, c j i₀ * f j (x p)) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [hc₀ j, zero_mul]
        rw [hi₀zero, zero_mul, zero_add] at hsplit
        exact hsplit.trans hp
      have hrest := ih (s.erase i₀) (Finset.erase_ssubset hi₀) c hrelationErase
      intro i hi j
      by_cases hii₀ : i = i₀
      · subst i
        exact hc₀ j
      · exact hrest i (Finset.mem_erase.mpr ⟨hii₀, hi⟩) j

/-- **Tail-dense asymptotic tensor-separation law.** A finite linearly independent family of
continuous constraint observables remains independent modulo finite support after tensoring with
every finite asymptotic scale. No relation can mix source geometry with scale position. -/
theorem cofiniteTailDenseOn_asymptoticScale_tensor_tailIndependent
    {P V I J : Type*} [TopologicalSpace V] [Fintype I] [Fintype J]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (w : I → P → ℂ) (hw : CofiniteAsymptoticScale w) :
    TailCoefficientIndependent (fun ji : J × I => fun p => f ji.1 (x p) * w ji.2 p) := by
  classical
  intro c hsupp
  have hrelation : ∀ᶠ p in cofinite,
      ∑ i ∈ (Finset.univ : Finset I), (∑ j, c (j, i) * f j (x p)) * w i p = 0 := by
    filter_upwards [hsupp.eventually_cofinite_notMem] with p hp
    have hpzero : ∑ ji, c ji * (f ji.1 (x p) * w ji.2 p) = 0 := not_ne_iff.mp hp
    rw [Fintype.sum_prod_type, Finset.sum_comm] at hpzero
    calc
      ∑ i ∈ (Finset.univ : Finset I), (∑ j, c (j, i) * f j (x p)) * w i p =
          ∑ i, ∑ j, c (j, i) * (f j (x p) * w i p) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := hpzero
  have hc := asymptoticScale_coefficients_zero_on_finset x K hx f hf hlinear w hw
    Finset.univ (fun j i => c (j, i)) hrelation
  funext ji
  exact hc ji.2 (Finset.mem_univ _) ji.1

end

end GaloisForLFunctions.HTGeometry
