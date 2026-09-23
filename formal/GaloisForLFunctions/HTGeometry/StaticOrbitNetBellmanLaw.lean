import GaloisForLFunctions.HTGeometry.EuclideanSphereCoveringBound
import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-!
# Static orbit nets and the local-gate Bellman recursion

A Lipschitz image of the Euclidean unit sphere has an `ε`-net of at most `(1 + 2L/ε)^m` points.
Applied through the Duhamel bound to the autonomous orbit of a norm-bounded coefficient
Hamiltonian, this produces a finite set of *actual orbit endpoints* covering the whole
Hamiltonian ensemble image at any fixed time.  Its logarithmic size is only `O(m log(|t|m/ε))`,
so target cardinality, covering entropy, and any purely geometric substitute for circuit
structure cannot separate a shallow-circuit image from an arbitrary orbit net.

The positive survivor is the exact local-gate recursion: reachable layers satisfy a one-step
union law, so the layer distance satisfies a min-plus Bellman recursion and every monotone
overlap reporter satisfies the corresponding max-plus recursion.  A robust Bellman calibration
lower-bounds approximate word complexity.
-/

open MeasureTheory Metric Set
open scoped BigOperators

namespace HTGeometry

/-! ## Norm-bounded coefficient Hamiltonians -/

section Coefficient

variable {m : ℕ} {A : Type*} [CStarAlgebra A]

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Hamiltonian assembled from real coefficients in a bounded self-adjoint dictionary. -/
noncomputable def coefficientHamiltonian (P : Fin m → A) (theta : E) : A :=
  ∑ a, theta a • P a

theorem isSelfAdjoint_coefficientHamiltonian {P : Fin m → A}
    (hP : ∀ a, IsSelfAdjoint (P a)) (theta : E) :
    IsSelfAdjoint (coefficientHamiltonian P theta) := by
  show star (∑ a, theta a • P a) = ∑ a, theta a • P a
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul, star_trivial, (hP a).star_eq]

/-- The euclidean `ℓ¹`–`ℓ²` comparison on `m` coordinates. -/
theorem sum_abs_le_sqrt_card_mul_norm (v : E) :
    ∑ a, |v a| ≤ Real.sqrt m * ‖v‖ := by
  have hsq : (∑ a, |v a|) ^ (2 : ℕ) ≤ (m : ℝ) * ∑ a, |v a| ^ (2 : ℕ) := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun a => |v a|)
    simpa using this
  have hnorm : ‖v‖ ^ (2 : ℕ) = ∑ a, |v a| ^ (2 : ℕ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
    · exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs]
    · positivity
  have hnn : 0 ≤ ∑ a, |v a| := Finset.sum_nonneg fun a _ => abs_nonneg _
  have hmn : 0 ≤ Real.sqrt m * ‖v‖ := by positivity
  have hle : (∑ a, |v a|) ^ (2 : ℕ) ≤ (Real.sqrt m * ‖v‖) ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), hnorm]
    exact hsq
  nlinarith [hnn, hmn, hle]

/-- Coefficient Hamiltonians are `√m`-Lipschitz in the coefficient vector. -/
theorem norm_coefficientHamiltonian_sub_le {P : Fin m → A}
    (hPnorm : ∀ a, ‖P a‖ ≤ 1) (theta theta' : E) :
    ‖coefficientHamiltonian P theta - coefficientHamiltonian P theta'‖ ≤
      Real.sqrt m * ‖theta - theta'‖ := by
  have hdiff : coefficientHamiltonian P theta - coefficientHamiltonian P theta' =
      ∑ a, (theta a - theta' a) • P a := by
    simp only [coefficientHamiltonian, ← Finset.sum_sub_distrib, sub_smul]
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ a : Fin m, ‖(theta a - theta' a) • P a‖ ≤ |(theta - theta') a| := by
    intro a
    rw [norm_smul, Real.norm_eq_abs]
    have := hPnorm a
    have habs : (0 : ℝ) ≤ |theta a - theta' a| := abs_nonneg _
    have hsub : (theta - theta') a = theta a - theta' a := rfl
    rw [hsub]
    nlinarith [norm_nonneg (P a)]
  refine le_trans (Finset.sum_le_sum fun a _ => hterm a) ?_
  exact sum_abs_le_sqrt_card_mul_norm (theta - theta')

/-- **Duhamel orbit Lipschitz bound.**  At fixed time the autonomous unitary of a coefficient
Hamiltonian is `|t|√m`-Lipschitz in the coefficient vector. -/
theorem norm_coefficientEvolution_sub_le {P : Fin m → A}
    (hP : ∀ a, IsSelfAdjoint (P a)) (hPnorm : ∀ a, ‖P a‖ ≤ 1) (t : ℝ) (theta theta' : E) :
    ‖NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta)) -
        NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta'))‖ ≤
      (|t| * Real.sqrt m) * ‖theta - theta'‖ := by
  have hduh := GaloisForLFunctions.HTGeometry.selfAdjoint_unitaryEvolution_norm_sub_le
    (coefficientHamiltonian P theta) (coefficientHamiltonian P theta')
    (isSelfAdjoint_coefficientHamiltonian hP theta)
    (isSelfAdjoint_coefficientHamiltonian hP theta') t
  have hlip := norm_coefficientHamiltonian_sub_le hPnorm theta theta'
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  calc ‖NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta)) -
        NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta'))‖
      ≤ |t| * ‖coefficientHamiltonian P theta - coefficientHamiltonian P theta'‖ := hduh
    _ ≤ |t| * (Real.sqrt m * ‖theta - theta'‖) := by
        exact mul_le_mul_of_nonneg_left hlip habs
    _ = (|t| * Real.sqrt m) * ‖theta - theta'‖ := by ring

/-- **Static orbit net.**  At any fixed time the whole coefficient-sphere orbit image is covered
to accuracy `ε` by at most `(1 + 2|t|√m/ε)^m` actual orbit endpoints. -/
theorem exists_staticOrbit_net [Nontrivial E] {P : Fin m → A}
    (hP : ∀ a, IsSelfAdjoint (P a)) (hPnorm : ∀ a, ‖P a‖ ≤ 1)
    {t eps : ℝ} (ht : t ≠ 0) (heps : 0 < eps) (hm : 0 < m) :
    ∃ Z : Finset A,
      (Z.card : ℝ) ≤ (1 + 2 * (|t| * Real.sqrt m) / eps) ^ m ∧
      (∀ z ∈ Z, ∃ theta ∈ Metric.sphere (0 : E) 1,
        NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta)) = z) ∧
      ∀ theta ∈ Metric.sphere (0 : E) 1, ∃ z ∈ Z,
        ‖NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta)) - z‖ ≤ eps := by
  have hL : 0 < |t| * Real.sqrt m := by
    have h1 : 0 < |t| := abs_pos.mpr ht
    have h2 : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    positivity
  obtain ⟨Z, hcard, him, hnet⟩ :=
    exists_unitSphere_lipschitz_net (m := m) (Y := A) heps hL
      (fun theta => NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta)))
      (fun x _ y _ => by
        simpa [dist_eq_norm] using norm_coefficientEvolution_sub_le hP hPnorm t x y)
  refine ⟨Z, hcard, him, ?_⟩
  intro theta htheta
  obtain ⟨z, hz, hd⟩ := hnet theta htheta
  exact ⟨z, hz, by simpa [dist_eq_norm] using hd⟩

end Coefficient

/-! ## The local-gate recursions -/

section Recursion

variable {X : Type*} [MetricSpace X] {Γ : Type*}
variable {act : Γ → X → X} {inv : Γ → Γ} {chi : X}

theorem infDist_union (x : X) (s t : Set X) (hs : s.Nonempty) (ht : t.Nonempty) :
    Metric.infDist x (s ∪ t) = min (Metric.infDist x s) (Metric.infDist x t) := by
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · exact Metric.infDist_le_infDist_of_subset Set.subset_union_left hs
    · exact Metric.infDist_le_infDist_of_subset Set.subset_union_right ht
  · refine (Metric.le_infDist (hs.mono Set.subset_union_left)).mpr ?_
    rintro y (hy | hy)
    · exact le_trans (min_le_left _ _) (Metric.infDist_le_dist_of_mem hy)
    · exact le_trans (min_le_right _ _) (Metric.infDist_le_dist_of_mem hy)

theorem infDist_image_act (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (g : Γ) (x : X) (S : Set X) :
    Metric.infDist x (act g '' S) = Metric.infDist (act (inv g) x) S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · refine le_antisymm ?_ ?_
    · refine (Metric.le_infDist hS).mpr fun z hz => ?_
      rw [← dist_act_left hiso hinvL g x z]
      exact Metric.infDist_le_dist_of_mem ⟨z, hz, rfl⟩
    · refine (Metric.le_infDist (hS.image (act g))).mpr ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [dist_act_left hiso hinvL g x z]
      exact Metric.infDist_le_dist_of_mem hz

/-- **Min-plus layer recursion.**  The distance to the `(s+1)`-st reachable layer is the minimum
of the distance to the `s`-th layer and the distances to that layer from each gate-pulled-back
point. -/
theorem layerDist_succ [Nonempty Γ] [Finite Γ]
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (s : ℕ) (x : X) :
    layerDist act chi (s + 1) x =
      min (layerDist act chi s x) (⨅ g : Γ, layerDist act chi s (act (inv g) x)) := by
  classical
  have hne : (reachSet act chi s).Nonempty := reachSet_nonempty act chi s
  have hunion : reachSet act chi (s + 1) =
      reachSet act chi s ∪ ⋃ g : Γ, act g '' reachSet act chi s := by
    rw [reachSet_succ]
    congr 1
    ext z
    constructor
    · rintro ⟨⟨g, y⟩, ⟨-, hy⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨g, ⟨y, hy, rfl⟩⟩
    · intro hz
      obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hz
      exact ⟨(g, y), ⟨Set.mem_univ _, hy⟩, rfl⟩
  have hiune : (⋃ g : Γ, act g '' reachSet act chi s).Nonempty := by
    obtain ⟨g⟩ := ‹Nonempty Γ›
    exact ⟨act g chi, Set.mem_iUnion.mpr ⟨g, ⟨chi, mem_reachSet_self act chi s, rfl⟩⟩⟩
  have hsplit : Metric.infDist x (⋃ g : Γ, act g '' reachSet act chi s) =
      ⨅ g : Γ, layerDist act chi s (act (inv g) x) := by
    refine le_antisymm ?_ ?_
    · refine le_ciInf fun g => ?_
      simp only [layerDist]
      rw [← infDist_image_act hiso hinvL g x (reachSet act chi s)]
      refine Metric.infDist_le_infDist_of_subset
        (Set.subset_iUnion (fun h : Γ => act h '' reachSet act chi s) g)
        ⟨act g chi, ⟨chi, mem_reachSet_self act chi s, rfl⟩⟩
    · refine (Metric.le_infDist hiune).mpr ?_
      intro y hy
      obtain ⟨g, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      have hb : BddBelow (Set.range fun g : Γ => layerDist act chi s (act (inv g) x)) := by
        refine ⟨0, ?_⟩
        rintro r ⟨g, rfl⟩
        exact Metric.infDist_nonneg
      refine le_trans (ciInf_le hb g) ?_
      simp only [layerDist]
      rw [← infDist_image_act hiso hinvL g x (reachSet act chi s)]
      exact Metric.infDist_le_dist_of_mem ⟨z, hz, rfl⟩
  rw [layerDist, layerDist, hunion, infDist_union x _ _ hne hiune, hsplit]


/-! ### Max-plus overlap recursion -/

omit [MetricSpace X] in
theorem finite_reachSet [Finite Γ] (act : Γ → X → X) (chi : X) (s : ℕ) :
    (reachSet act chi s).Finite := by
  induction s with
  | zero => rw [reachSet_zero]; exact Set.finite_singleton _
  | succ s ih =>
      rw [reachSet_succ]
      exact ih.union ((Set.finite_univ.prod ih).image _)

omit [MetricSpace X] in
theorem image_reachSet_succ {pair : X → X → ℝ} {pull : Γ → X → X}
    (hpair : ∀ (g : Γ) (z v : X), pair (act g z) v = pair z (pull g v))
    (s : ℕ) (v : X) :
    (fun z => pair z v) '' reachSet act chi (s + 1) =
      ((fun z => pair z v) '' reachSet act chi s) ∪
        ⋃ g : Γ, ((fun z => pair z (pull g v)) '' reachSet act chi s) := by
  rw [reachSet_succ, Set.image_union]
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨⟨g, y⟩, ⟨-, hy⟩, rfl⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨g, ⟨y, hy, (hpair g y v).symm⟩⟩
  · intro hr
    obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hr
    exact ⟨act g y, ⟨(g, y), ⟨Set.mem_univ _, hy⟩, rfl⟩, hpair g y v⟩

omit [MetricSpace X] in
/-- **Max-plus overlap recursion.**  Any pairing that intertwines the gate action with its
inverse on the second argument obeys the one-gate max-plus Bellman law on reachable layers. -/
theorem sSup_image_reachSet_succ [Finite Γ] [Nonempty Γ] {pair : X → X → ℝ} {pull : Γ → X → X}
    (hpair : ∀ (g : Γ) (z v : X), pair (act g z) v = pair z (pull g v))
    (s : ℕ) (v : X) :
    sSup ((fun z => pair z v) '' reachSet act chi (s + 1)) =
      max (sSup ((fun z => pair z v) '' reachSet act chi s))
        (⨆ g : Γ, sSup ((fun z => pair z (pull g v)) '' reachSet act chi s)) := by
  classical
  have hfin := finite_reachSet act chi s
  have hne := reachSet_nonempty act chi s
  have himfin : ∀ w : X, ((fun z => pair z w) '' reachSet act chi s).Finite :=
    fun w => hfin.image _
  have himne : ∀ w : X, ((fun z => pair z w) '' reachSet act chi s).Nonempty :=
    fun w => hne.image _
  have hbdd : ∀ w : X, BddAbove ((fun z => pair z w) '' reachSet act chi s) :=
    fun w => (himfin w).bddAbove
  set T : Set ℝ := ⋃ g : Γ, ((fun z => pair z (pull g v)) '' reachSet act chi s) with hT
  have hTfin : T.Finite := Set.finite_iUnion fun g => himfin _
  have hTne : T.Nonempty := by
    obtain ⟨g⟩ := ‹Nonempty Γ›
    obtain ⟨r, hr⟩ := himne (pull g v)
    exact ⟨r, Set.mem_iUnion.mpr ⟨g, hr⟩⟩
  have hTsup : sSup T = ⨆ g : Γ, sSup ((fun z => pair z (pull g v)) '' reachSet act chi s) := by
    have hbddSup : BddAbove (Set.range fun g : Γ =>
        sSup ((fun z => pair z (pull g v)) '' reachSet act chi s)) :=
      (Set.finite_range _).bddAbove
    refine le_antisymm (csSup_le hTne ?_) (ciSup_le fun g => ?_)
    · intro r hr
      obtain ⟨g, hrg⟩ := Set.mem_iUnion.mp hr
      exact le_trans (le_csSup (hbdd _) hrg) (le_ciSup hbddSup g)
    · exact csSup_le (himne _) fun r hr =>
        le_csSup hTfin.bddAbove (Set.mem_iUnion.mpr ⟨g, hr⟩)
  rw [image_reachSet_succ hpair s v, ← hT,
    csSup_union (hbdd v) (himne v) hTfin.bddAbove hTne, hTsup]


/-- A monotone reader commutes with a finite supremum. -/
theorem Monotone.map_ciSup_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    {B : ℝ → ℝ} (hB : Monotone B) (f : ι → ℝ) :
    B (⨆ i, f i) = ⨆ i, B (f i) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
  have hbf : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  have hbBf : BddAbove (Set.range fun i => B (f i)) := (Set.finite_range _).bddAbove
  have h1 : (⨆ i, f i) = f i₀ := le_antisymm (ciSup_le hi₀) (le_ciSup hbf i₀)
  have h2 : (⨆ i, B (f i)) = B (f i₀) :=
    le_antisymm (ciSup_le fun i => hB (hi₀ i)) (le_ciSup hbBf i₀)
  rw [h1, h2]

omit [MetricSpace X] in
/-- **Monotone max-plus reporter law.**  Every increasing reader of the overlap reporter obeys the
same one-gate max-plus recursion. -/
theorem sSup_image_reachSet_succ_monotone [Finite Γ] [Nonempty Γ]
    {pair : X → X → ℝ} {pull : Γ → X → X} {B : ℝ → ℝ} (hB : Monotone B)
    (hpair : ∀ (g : Γ) (z v : X), pair (act g z) v = pair z (pull g v))
    (s : ℕ) (v : X) :
    B (sSup ((fun z => pair z v) '' reachSet act chi (s + 1))) =
      max (B (sSup ((fun z => pair z v) '' reachSet act chi s)))
        (⨆ g : Γ, B (sSup ((fun z => pair z (pull g v)) '' reachSet act chi s))) := by
  rw [sSup_image_reachSet_succ hpair s v, hB.map_max,
    Monotone.map_ciSup_of_finite hB]

end Recursion


/-! ## Unitary overlap reporters -/

section Unitary

variable {Γ : Type*} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Overlap recursion for unitary gates.**  The largest squared overlap with the `(s+1)`-st
reachable layer is the maximum of the `s`-th layer value and its values at the adjoint-pulled-back
argument. -/
theorem sSup_unitaryOverlap_reachSet_succ [Finite Γ] [Nonempty Γ]
    (u : Γ → (V ≃ₗᵢ[ℂ] V)) (chi : V) (s : ℕ) (v : V) :
    sSup ((fun z => ‖(inner ℂ z v : ℂ)‖ ^ (2 : ℕ)) ''
        reachSet (fun g => (u g : V → V)) chi (s + 1)) =
      max (sSup ((fun z => ‖(inner ℂ z v : ℂ)‖ ^ (2 : ℕ)) ''
            reachSet (fun g => (u g : V → V)) chi s))
        (⨆ g : Γ, sSup ((fun z => ‖(inner ℂ z ((u g).symm v) : ℂ)‖ ^ (2 : ℕ)) ''
            reachSet (fun g => (u g : V → V)) chi s)) := by
  refine sSup_image_reachSet_succ (act := fun g => (u g : V → V))
    (pair := fun z v => ‖(inner ℂ z v : ℂ)‖ ^ (2 : ℕ))
    (pull := fun g v => (u g).symm v) ?_ s v
  intro g z w
  have : (inner ℂ ((u g) z) w : ℂ) = (inner ℂ z ((u g).symm w) : ℂ) := by
    conv_lhs => rw [← (u g).apply_symm_apply w]
    exact (u g).inner_map_map z ((u g).symm w)
  rw [this]

end Unitary

/-! ## Robust Bellman calibration -/

section Calibration

variable {X : Type*} [MetricSpace X] {Γ : Type*}
variable {act : Γ → X → X} {chi : X}

/-- **Robust Bellman calibration lower bound.**  A gate-Lipschitz calibration certifies an
approximate word-complexity lower bound. -/
theorem le_length_of_bellmanCalibration {Phi : X → ℝ} {L eps : ℝ} (hL : 0 ≤ L)
    (hgate : ∀ (g : Γ) (x : X), Phi (act g x) ≤ Phi x + 1)
    (hlip : ∀ u v : X, Phi u - Phi v ≤ L * dist u v)
    (v : X) (w : List Γ) (hw : dist (wordAct act w chi) v ≤ eps) :
    Phi v - Phi chi - L * eps ≤ (w.length : ℝ) := by
  have hword : ∀ (u : List Γ), Phi (wordAct act u chi) ≤ Phi chi + u.length := by
    intro u
    induction u with
    | nil => simp
    | cons g u ih =>
        have h := hgate g (wordAct act u chi)
        have : Phi (wordAct act u chi) ≤ Phi chi + (u.length : ℝ) := ih
        simp only [wordAct_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
  have hclose : Phi v - Phi (wordAct act w chi) ≤ L * eps := by
    refine le_trans (hlip v (wordAct act w chi)) ?_
    rw [dist_comm] at hw
    exact mul_le_mul_of_nonneg_left hw hL
  have := hword w
  linarith

end Calibration

end HTGeometry
