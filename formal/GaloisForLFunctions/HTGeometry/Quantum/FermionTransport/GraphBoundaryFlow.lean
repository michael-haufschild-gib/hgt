import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphFlow

/-!
# Instantaneous interior regularization of finite Fermi–Dirac transport

A zero occupation at positive time was zero at all earlier times at
that vertex. At an earlier time the derivative vanishes, so the
particle–hole equation forces every incoming occupation to vanish.
Vacancies propagate in the same way, with outgoing rates. On a
connected graph any nontrivial mass therefore gives interior states
at every positive time, and free-energy decay starts at time zero.
-/

open Set Filter
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

variable {V : Type*} [Fintype V] {G : WeightedGraph V} {E : V → ℝ} {x : ℝ → V → ℝ}

private theorem positive_of_exp_monotone {z : ℝ → ℝ} (a : ℝ)
    (h : MonotoneOn (fun t => Real.exp (a * t) * z t) (Ici 0)) (h₀ : 0 < z 0)
    (t : ℝ) (ht : 0 ≤ t) : 0 < z t := by
  have hn := h (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul] at hn
  by_contra! hz
  exact (not_le_of_gt h₀) (hn.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hz))

private theorem zero_backwards_of_exp_monotone {z : ℝ → ℝ} (a : ℝ)
    (h : MonotoneOn (fun t => Real.exp (a * t) * z t) (Ici 0))
    (hn : ∀ s : ℝ, 0 ≤ s → 0 ≤ z s) {t : ℝ} (ht : 0 ≤ t) (hz : z t = 0) :
    ∀ s ∈ Icc 0 t, z s = 0 := by
  intro s hs
  have hle := h (mem_Ici.mpr hs.1) (mem_Ici.mpr ht) hs.2
  change Real.exp (a * s) * z s ≤ Real.exp (a * t) * z t at hle
  rw [hz, mul_zero] at hle
  refine (le_of_not_gt fun hp => (not_lt_of_ge hle) (mul_pos (Real.exp_pos _) hp)).antisymm ?_
  exact hn s hs.1

private theorem zero_drift_of_constant_before (h : IsBoxOccupationFlow G E x)
    (v : V) {t c : ℝ} (ht : 0 < t) (hc : ∀ s ∈ Icc 0 t, x s v = c) :
    clippedDrift G E (x (t / 2)) v = 0 := by
  have hs : 0 < t / 2 := by positivity
  have hb : t / 2 < t := by linarith only [ht]
  have he : (fun r => x r v) =ᶠ[nhds (t / 2)] (fun _ => c) := by
    filter_upwards [Ioo_mem_nhds hs hb] with r hr
    exact hc r ⟨hr.1.le, hr.2.le⟩
  have hd := (hasDerivAt_const (t / 2) c).congr_of_eventuallyEq he
  exact (h.hasDerivAt_coordinate (t / 2) hs.le v).deriv.symm.trans hd.deriv

private theorem empty_neighbor_of_empty (h : IsBoxOccupationFlow G E x) {u v : V}
    (hw : 0 < G.w u v) {t : ℝ} (ht : 0 < t) (hz : x t v = 0) : x (t / 2) u = 0 := by
  have hs : 0 ≤ t / 2 := by positivity
  have hst : t / 2 ≤ t := by linarith only [ht]
  have hback := zero_backwards_of_exp_monotone (graphRateBound G E v) (h.occupation_exp_monotone v)
    (fun s hs => (h.in_box s hs v).1) ht.le hz
  have hd := zero_drift_of_constant_before h v ht hback
  have he : (∑ i, G.w v i * Real.exp (E i) * x (t / 2) i) = 0 := by
    rw [clippedDrift_eq_of_box G E _ (h.in_box (t / 2) hs) v, hback _ ⟨hs, hst⟩] at hd
    simpa only [sub_zero, mul_one, mul_zero, zero_mul] using hd
  have hnonneg (i : V) : 0 ≤ G.w v i * Real.exp (E i) * x (t / 2) i :=
    mul_nonneg (mul_nonneg (G.w_nonneg v i) (Real.exp_pos _).le) (h.in_box _ hs i).1
  have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp he u (Finset.mem_univ _)
  have hw' : 0 < G.w v u := by rwa [G.w_symm v u]
  exact (mul_eq_zero.mp hu).resolve_left (mul_pos hw' (Real.exp_pos _)).ne'

private theorem full_neighbor_of_full (h : IsBoxOccupationFlow G E x) {u v : V}
    (hw : 0 < G.w u v) {t : ℝ} (ht : 0 < t) (hz : x t v = 1) : x (t / 2) u = 1 := by
  have hs : 0 ≤ t / 2 := by positivity
  have hst : t / 2 ≤ t := by linarith only [ht]
  have hback_vacancy := zero_backwards_of_exp_monotone (graphRateBound G E v) (h.vacancy_exp_monotone v)
    (fun s hs => sub_nonneg.mpr (h.in_box s hs v).2) ht.le (sub_eq_zero.mpr hz.symm)
  have hback (s : ℝ) (hs : s ∈ Icc 0 t) : x s v = 1 :=
    (sub_eq_zero.mp (hback_vacancy s hs)).symm
  have hd := zero_drift_of_constant_before h v ht hback
  have he : (∑ i, G.w v i * Real.exp (E v) * (1 - x (t / 2) i)) = 0 := by
    rw [clippedDrift_eq_of_box G E _ (h.in_box (t / 2) hs) v, hback _ ⟨hs, hst⟩] at hd
    apply neg_eq_zero.mp
    simpa only [sub_self, mul_zero, one_mul, zero_sub, Finset.sum_neg_distrib] using hd
  have hnonneg (i : V) : 0 ≤ G.w v i * Real.exp (E v) * (1 - x (t / 2) i) :=
    mul_nonneg (mul_nonneg (G.w_nonneg v i) (Real.exp_pos _).le) (sub_nonneg.mpr (h.in_box _ hs i).2)
  have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp he u (Finset.mem_univ _)
  have hw' : 0 < G.w v u := by rwa [G.w_symm v u]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left (mul_pos hw' (Real.exp_pos _)).ne')).symm

/-- Any positive initial occupation propagates instantly along every positive-weight path. -/
theorem IsBoxOccupationFlow.pos_of_path (h : IsBoxOccupationFlow G E x) {u v : V}
    (hu : 0 < x 0 u) (hp : Relation.ReflTransGen (fun a b => 0 < G.w a b) u v) :
    ∀ t : ℝ, 0 < t → 0 < x t v := by
  induction hp with
  | refl =>
    exact fun t ht => positive_of_exp_monotone _ (h.occupation_exp_monotone u) hu t ht.le
  | @tail a b _ hw ih =>
    intro t ht
    by_contra! hn
    have hz := hn.antisymm (h.in_box t ht.le b).1
    exact (ih (t / 2) (by positivity)).ne' (empty_neighbor_of_empty h hw ht hz)

/-- Any positive initial vacancy propagates instantly along every positive-weight path. -/
theorem IsBoxOccupationFlow.vacancy_pos_of_path (h : IsBoxOccupationFlow G E x) {u v : V}
    (hu : 0 < 1 - x 0 u) (hp : Relation.ReflTransGen (fun a b => 0 < G.w a b) u v) :
    ∀ t : ℝ, 0 < t → 0 < 1 - x t v := by
  induction hp with
  | refl =>
    exact fun t ht => positive_of_exp_monotone _ (h.vacancy_exp_monotone u) hu t ht.le
  | @tail a b _ hw ih =>
    intro t ht
    by_contra! hn
    have hz := (sub_eq_zero.mp (hn.antisymm (sub_nonneg.mpr (h.in_box t ht.le b).2))).symm
    have he : 1 - x (t / 2) a = 0 := sub_eq_zero.mpr (full_neighbor_of_full h hw ht hz).symm
    exact (ih (t / 2) (by positivity)).ne' he

omit [Fintype V] in
private theorem reverse_positive_path {u v : V}
    (h : Relation.ReflTransGen (fun a b => 0 < G.w a b) u v) :
    Relation.ReflTransGen (fun a b => 0 < G.w a b) v u := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hw ih =>
    have hw' : 0 < G.w b a := by rwa [G.w_symm b a]
    exact (Relation.ReflTransGen.single (r := fun i j => 0 < G.w i j) hw').trans ih

/-- Occupation is conserved separately on every set with zero edge weights across its cut. -/
theorem IsBoxOccupationFlow.mass_on_zero_cut (h : IsBoxOccupationFlow G E x) (S : Finset V)
    (hcut : ∀ v ∈ S, ∀ u ∉ S, G.w v u = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∑ v ∈ S, x t v) = ∑ v ∈ S, x 0 v := by
  let m (s : ℝ) := ∑ v ∈ S, x s v
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt m 0 s := by
    let J (v u : V) := G.w v u * (Real.exp (E u) * (x s u * (1 - x s v)) -
      Real.exp (E v) * (x s v * (1 - x s u)))
    have hfull (v : V) : clippedDrift G E (x s) v = ∑ u, J v u := by
      rw [clippedDrift_eq_of_box G E _ (h.in_box s hs) v]
      exact Finset.sum_congr rfl fun u _ => by dsimp only [J]; ring
    have hrow (v : V) (hv : v ∈ S) : (∑ u ∈ S, J v u) = ∑ u, J v u := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro u _ hu
      dsimp only [J]
      rw [hcut v hv u hu, zero_mul]
    have hswap : (∑ v ∈ S, ∑ u ∈ S, J v u) = -(∑ v ∈ S, ∑ u ∈ S, J v u) := by
      conv_lhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
      dsimp only [J]
      rw [G.w_symm u v]
      ring
    have hz : (∑ v ∈ S, clippedDrift G E (x s) v) = 0 := by
      calc
        _ = ∑ v ∈ S, ∑ u ∈ S, J v u :=
          Finset.sum_congr rfl fun v hv => (hfull v).trans (hrow v hv).symm
        _ = 0 := by linarith only [hswap]
    have hsum : HasDerivAt m (∑ v ∈ S, clippedDrift G E (x s) v) s :=
      HasDerivAt.fun_sum (fun v _ => h.hasDerivAt_coordinate s hs v)
    rwa [hz] at hsum
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := m) (f' := fun _ => (0 : ℝ))
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun _ _ => le_of_eq norm_zero) (convex_Ici 0)
    (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht)
  rw [zero_mul] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (hb.antisymm (norm_nonneg _)))

private noncomputable def predecessors (G : WeightedGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => Relation.ReflTransGen (fun a b => 0 < G.w a b) u v)

private theorem mem_predecessors (G : WeightedGraph V) (u v : V) :
    u ∈ predecessors G v ↔ Relation.ReflTransGen (fun a b => 0 < G.w a b) u v := by
  classical
  simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem predecessors_zero_cut (G : WeightedGraph V) (v : V) :
    ∀ a ∈ predecessors G v, ∀ b ∉ predecessors G v, G.w a b = 0 := by
  intro a ha b hb
  refine (le_of_not_gt fun hab => hb ((mem_predecessors G b v).mpr ?_)).antisymm (G.w_nonneg a b)
  have hba : 0 < G.w b a := by rwa [G.w_symm b a]
  exact (Relation.ReflTransGen.single (r := fun i j => 0 < G.w i j) hba).trans
    ((mem_predecessors G a v).mp ha)

omit [Fintype V] in
private theorem positive_seed_of_equal_sum (S : Finset V) (f g : V → ℝ)
    (hf : ∀ u ∈ S, 0 ≤ f u) (hg : ∀ u ∈ S, 0 ≤ g u)
    (hs : (∑ u ∈ S, f u) = ∑ u ∈ S, g u) {v : V} (hv : v ∈ S) (hpos : 0 < f v) :
    ∃ u ∈ S, 0 < g u := by
  by_contra! hz
  have hzero : (∑ u ∈ S, g u) = 0 :=
    Finset.sum_eq_zero (fun u hu => (hz u hu).antisymm (hg u hu))
  exact hpos.ne' ((Finset.sum_eq_zero_iff_of_nonneg hf).mp (hs.trans hzero) v hv)

/-- At any positive time, a vertex is occupied exactly when its component
contained particles initially. -/
theorem IsBoxOccupationFlow.pos_iff_initial_particle (h : IsBoxOccupationFlow G E x)
    (v : V) {t : ℝ} (ht : 0 < t) :
    0 < x t v ↔ ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < x 0 u := by
  constructor
  · intro hv
    have hmass := h.mass_on_zero_cut (predecessors G v) (predecessors_zero_cut G v) ht.le
    obtain ⟨u, hu, hp⟩ := positive_seed_of_equal_sum (predecessors G v) (x t) (x 0)
      (fun u _ => (h.in_box t ht.le u).1) (fun u _ => (h.in_box 0 le_rfl u).1) hmass
      ((mem_predecessors G v v).mpr .refl) hv
    exact ⟨u, (mem_predecessors G u v).mp hu, hp⟩
  · rintro ⟨u, hu, hp⟩
    exact h.pos_of_path hp hu t ht

/-- At any positive time, a vertex has a vacancy exactly when its component
contained vacancies initially. -/
theorem IsBoxOccupationFlow.vacancy_pos_iff_initial_vacancy (h : IsBoxOccupationFlow G E x)
    (v : V) {t : ℝ} (ht : 0 < t) :
    0 < 1 - x t v ↔ ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < 1 - x 0 u := by
  constructor
  · intro hv
    let S := predecessors G v
    have hmass : (∑ u ∈ S, (1 - x t u)) = ∑ u ∈ S, (1 - x 0 u) := by
      simp only [Finset.sum_sub_distrib, h.mass_on_zero_cut S (predecessors_zero_cut G v) ht.le]
    obtain ⟨u, hu, hp⟩ := positive_seed_of_equal_sum S (fun u => 1 - x t u) (fun u => 1 - x 0 u)
      (fun u _ => sub_nonneg.mpr (h.in_box t ht.le u).2)
      (fun u _ => sub_nonneg.mpr (h.in_box 0 le_rfl u).2) hmass ((mem_predecessors G v v).mpr .refl) hv
    exact ⟨u, (mem_predecessors G u v).mp hu, hp⟩
  · rintro ⟨u, hu, hp⟩
    exact h.vacancy_pos_of_path hp hu t ht

/-- Nontrivial total mass on a connected graph gives interior occupations at every positive time. -/
theorem IsBoxOccupationFlow.interior_of_nontrivial_mass (h : IsBoxOccupationFlow G E x)
    (root : V) (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v)
    (hm : (∑ v, x 0 v) ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ)) :
    ∀ t : ℝ, 0 < t → ∀ v : V, x t v ∈ Ioo 0 1 := by
  have hparticle : ∃ u, 0 < x 0 u := by
    by_contra! hz
    have hs : (∑ v, x 0 v) = 0 :=
      Finset.sum_eq_zero (fun v _ => (hz v).antisymm (h.in_box 0 le_rfl v).1)
    exact hm.1.ne' hs
  have hvacancy : ∃ u, 0 < 1 - x 0 u := by
    by_contra! hz
    have he (v : V) : x 0 v = 1 :=
      (sub_eq_zero.mp ((hz v).antisymm (sub_nonneg.mpr (h.in_box 0 le_rfl v).2))).symm
    have hs : (∑ v, x 0 v) = (Fintype.card V : ℝ) := by
      simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact hm.2.ne hs
  obtain ⟨u, hu⟩ := hparticle
  obtain ⟨w, hw⟩ := hvacancy
  intro t ht v
  exact ⟨h.pos_of_path hu ((reverse_positive_path (hpath u)).trans (hpath v)) t ht,
    sub_pos.mp (h.vacancy_pos_of_path hw ((reverse_positive_path (hpath w)).trans (hpath v)) t ht)⟩

/-- At zero total mass the box flow stays completely empty. -/
theorem IsBoxOccupationFlow.eq_zero_of_zero_mass (h : IsBoxOccupationFlow G E x)
    (hm : (∑ v, x 0 v) = 0) {t : ℝ} (ht : 0 ≤ t) : x t = 0 := by
  have hs := (h.mass_eq ht).trans hm
  funext v
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (h.in_box t ht i).1)).mp hs v (Finset.mem_univ _)

/-- At full total mass the box flow stays completely full. -/
theorem IsBoxOccupationFlow.eq_one_of_full_mass (h : IsBoxOccupationFlow G E x)
    (hm : (∑ v, x 0 v) = (Fintype.card V : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    x t = fun _ => 1 := by
  have hs : (∑ v, (1 - x t v)) = 0 := by
    rw [Finset.sum_sub_distrib, h.mass_eq ht, hm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_self]
  have hv := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (h.in_box t ht i).2)).mp hs
  funext v
  exact (sub_eq_zero.mp (hv v (Finset.mem_univ _))).symm

/-- For any nontrivial mass on a connected graph, free-energy excess
and squared occupation error decay exponentially from the initial state,
including when some initial coordinates are empty or full. -/
theorem IsBoxOccupationFlow.exponential_relaxation (h : IsBoxOccupationFlow G E x)
    (root : V) (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v)
    (hm : (∑ v, x 0 v) ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ)) :
    ∃ μ k : ℝ, 0 < k ∧ gibbsMass E μ = (∑ v, x 0 v) ∧ ∀ t : ℝ, 0 ≤ t →
      let q (v : V) := (gibbsOccupation (E v) μ : ℝ)
      let M := Real.exp (-(k * t)) * (freeEnergy E (x 0) - freeEnergy E q)
      freeEnergy E (x t) - freeEnergy E q ≤ M ∧ 2 * ∑ v, (x t v - q v) ^ 2 ≤ M :=
  h.exponential_relaxation_of_positive_interior root hpath hm (h.interior_of_nontrivial_mass root hpath hm)

#print axioms IsBoxOccupationFlow.pos_of_path
#print axioms IsBoxOccupationFlow.vacancy_pos_of_path
#print axioms IsBoxOccupationFlow.mass_on_zero_cut
#print axioms IsBoxOccupationFlow.pos_iff_initial_particle
#print axioms IsBoxOccupationFlow.vacancy_pos_iff_initial_vacancy
#print axioms IsBoxOccupationFlow.interior_of_nontrivial_mass
#print axioms IsBoxOccupationFlow.eq_zero_of_zero_mass
#print axioms IsBoxOccupationFlow.eq_one_of_full_mass
#print axioms IsBoxOccupationFlow.exponential_relaxation

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
