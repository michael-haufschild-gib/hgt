import GaloisForLFunctions.HTGeometry.DbarAltForms
import GaloisForLFunctions.HTGeometry.DbarPuncturedSolve

/-!
# The Dolbeault system in degree at least two on an exhausted domain

In degrees `q ≥ 1` the passage from local to global solvability of `∂̄u = f` needs no
approximation.  If `u` solves the system on one stage of an exhaustion and `v` solves it on the
next, their difference is `∂̄`-closed and of degree `q ≥ 1`, hence itself exact on the smaller
stage; subtracting the differential of that primitive from `v` produces a solution on the larger
stage that agrees with `u` on the smaller one.  The sequence of solutions is therefore eventually
constant at every point, and the pointwise limit is a global solution.

This is the mechanism that replaces the Laurent and Runge estimates used in degree `1`, where the
correction is only holomorphic and the sequence merely converges.

* `HTGeometry.setDbar_exhaustion_solve` : the abstract statement, for any exhaustion on which the
  system is locally solvable in every degree.
* `HTGeometry.setDbar_global_solve` : the case of `ℂ^n`.
* `HTGeometry.setDbar_punctured_solve` : the case of `(ℂ^×)^n`.
-/

namespace HTGeometry

open Complex

section Local

variable {n : ℕ}

/-- A form is smooth on a set when all its coefficients are smooth at each of its points. -/
def SmoothSetFormOn (f : SetForm n) (X : Set (Fin n → ℂ)) : Prop :=
  ∀ (S : Finset (Fin n)), ∀ z ∈ X, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f S) z

theorem SmoothSetForm.smoothOn {f : SetForm n} (hf : SmoothSetForm f) (X : Set (Fin n → ℂ)) :
    SmoothSetFormOn f X := fun S _ _ => (hf S).contDiffAt

/-- **The Dolbeault operator is local.**  Two forms agreeing near a point have the same
differential there. -/
theorem setDbar_congr_of_eventuallyEq {f g : SetForm n} {z : Fin n → ℂ}
    (h : ∀ S : Finset (Fin n), ∀ᶠ y in nhds z, f S y = g S y) (S : Finset (Fin n)) :
    setDbar f S z = setDbar g S z := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dzbarAt_congr_of_eventuallyEq (h (S.erase k))]

/-- The differential of a form agreeing with a smooth form on an open set is computed by that
smooth form. -/
theorem setDbar_congr_on_isOpen {f g : SetForm n} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hfg : ∀ S : Finset (Fin n), ∀ y ∈ U, f S y = g S y) {z : Fin n → ℂ} (hz : z ∈ U)
    (S : Finset (Fin n)) : setDbar f S z = setDbar g S z :=
  setDbar_congr_of_eventuallyEq
    (fun T => Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => hfg T y hy) S

end Local

section Exhaustion

variable {n : ℕ}

/-- A primitive of `f` of degree `q + 1` on the stage `E (m + 1)` of an exhaustion. -/
def DbarPrimitiveOn (E : ℕ → Set (Fin n → ℂ)) (f : SetForm n) (q m : ℕ) (u : SetForm n) : Prop :=
  SmoothSetForm u ∧ SetFormDeg (q + 1) u ∧
    ∀ S : Finset (Fin n), ∀ z ∈ E (m + 1), setDbar u S z = f S z

/-- The Dolbeault system is solvable from one stage of an exhaustion to the previous one, in every
degree. -/
def DbarStageSolvable (E : ℕ → Set (Fin n → ℂ)) (X : Set (Fin n → ℂ)) : Prop :=
  ∀ (m q : ℕ) (g : SetForm n), SmoothSetFormOn g X → SetFormDeg (q + 1) g →
    (∀ S : Finset (Fin n), ∀ z ∈ E (m + 1), setDbar g S z = 0) →
    ∃ w : SetForm n, SmoothSetForm w ∧ SetFormDeg q w ∧
      ∀ S : Finset (Fin n), ∀ z ∈ E m, setDbar w S z = g S z

/-- The step of the stabilizing induction: a primitive on one stage is corrected to a primitive on
the next stage without changing it on the previous one.  The correction is the differential of a
primitive of the difference of the two solutions, which exists because that difference is closed
and of degree `q + 1 ≥ 1`. -/
theorem dbarPrimitiveOn_step {E : ℕ → Set (Fin n → ℂ)} {X : Set (Fin n → ℂ)}
    (hEmono : ∀ m, E m ⊆ E (m + 1))
    (hsolve : DbarStageSolvable E X) {f : SetForm n} (hCf : SmoothSetFormOn f X) {q : ℕ}
    (hdeg : SetFormDeg (q + 2) f)
    (hclosed : ∀ (m : ℕ) (S : Finset (Fin n)), ∀ z ∈ E m, setDbar f S z = 0)
    (m : ℕ) (u : SetForm n) (hu : DbarPrimitiveOn E f q m u) :
    ∃ u' : SetForm n, DbarPrimitiveOn E f q (m + 1) u' ∧
      ∀ S : Finset (Fin n), ∀ z ∈ E m, u' S z = u S z := by
  obtain ⟨hCu, hdu, hueq⟩ := hu
  obtain ⟨v, hCv, hdv, hveq⟩ :=
    hsolve (m + 2) (q + 1) f hCf hdeg (fun S z hz => hclosed (m + 3) S z hz)
  have hCg : SmoothSetForm (setFormSub v u) := hCv.sub hCu
  have hCgOn : SmoothSetFormOn (setFormSub v u) X := hCg.smoothOn X
  have hdg : SetFormDeg (q + 1) (setFormSub v u) := hdv.sub hdu
  have hgclosed : ∀ S : Finset (Fin n), ∀ z ∈ E (m + 1), setDbar (setFormSub v u) S z = 0 := by
    intro S z hz
    rw [setDbar_sub hCv hCu S z, hveq S z (hEmono (m + 1) hz), hueq S z hz, sub_self]
  obtain ⟨w, hCw, hdw, hweq⟩ := hsolve m q _ hCgOn hdg hgclosed
  refine ⟨setFormSub v (setDbar w), ⟨hCv.sub (setDbar_smooth hCw), hdv.sub (setDbar_deg hdw),
    fun S z hz => ?_⟩, fun S z hz => ?_⟩
  · rw [setDbar_sub hCv (setDbar_smooth hCw) S z,
      setDbar_setDbar_eq_zero (fun T => (hCw T).of_le (by decide)) S z, sub_zero]
    exact hveq S z hz
  · show v S z - setDbar w S z = u S z
    rw [hweq S z hz]
    show v S z - (v S z - u S z) = u S z
    ring

/-- **The Dolbeault system in degree at least two is globally solvable on an exhausted domain.**
The stagewise solutions are stabilized by subtracting the differential of a primitive of their
successive differences, so they are eventually constant at every point; the pointwise limit is
smooth because it agrees with one of them on a neighbourhood of each point. -/
theorem setDbar_exhaustion_solve {E : ℕ → Set (Fin n → ℂ)} (hEopen : ∀ m, IsOpen (E m))
    (hEmono : ∀ m, E m ⊆ E (m + 1)) {X : Set (Fin n → ℂ)} (hsolve : DbarStageSolvable E X)
    (hEsub : ∀ m, E m ⊆ X) (hEcover : ∀ z ∈ X, ∃ m, z ∈ E m)
    {q : ℕ} {f : SetForm n} (hCf : SmoothSetFormOn f X) (hdeg : SetFormDeg (q + 2) f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ X, setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetFormOn u X ∧ SetFormDeg (q + 1) u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ X, setDbar u S z = f S z := by
  classical
  have hclosed' : ∀ (m : ℕ) (S : Finset (Fin n)), ∀ z ∈ E m, setDbar f S z = 0 :=
    fun m S z hz => hclosed S z (hEsub m hz)
  have hEmono' : ∀ j k : ℕ, j ≤ k → E j ⊆ E k := by
    intro j k hjk
    induction k with
    | zero => rw [Nat.le_zero.1 hjk]
    | succ l ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hjk) with h | h
        · exact (ih (Nat.lt_succ_iff.1 h)).trans (hEmono l)
        · rw [h]
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : SetForm n, DbarPrimitiveOn E f q 0 u₀ := by
    obtain ⟨w, hCw, hdw, hweq⟩ :=
      hsolve 1 (q + 1) f hCf hdeg (fun S z hz => hclosed' 2 S z hz)
    exact ⟨w, hCw, hdw, hweq⟩
  have hstepex : ∀ (m : ℕ) (u : SetForm n), ∃ u' : SetForm n,
      DbarPrimitiveOn E f q m u → (DbarPrimitiveOn E f q (m + 1) u' ∧
        ∀ S : Finset (Fin n), ∀ z ∈ E m, u' S z = u S z) := by
    intro m u
    by_cases h : DbarPrimitiveOn E f q m u
    · obtain ⟨u', h1, h2⟩ := dbarPrimitiveOn_step hEmono hsolve hCf hdeg hclosed' m u h
      exact ⟨u', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨u, fun h' => absurd h' h⟩
  choose step hstep using hstepex
  obtain ⟨useq, huseq0, huseqS⟩ : ∃ useq : ℕ → SetForm n,
      useq 0 = u₀ ∧ ∀ j : ℕ, useq (j + 1) = step j (useq j) :=
    ⟨fun m => Nat.rec u₀ (fun j w => step j w) m, rfl, fun _ => rfl⟩
  have hGood : ∀ m : ℕ, DbarPrimitiveOn E f q m (useq m) := by
    intro m
    induction m with
    | zero => rw [huseq0]; exact hu₀
    | succ j ih => rw [huseqS j]; exact (hstep j (useq j) ih).1
  have hLink : ∀ (m : ℕ) (S : Finset (Fin n)), ∀ z ∈ E m, useq (m + 1) S z = useq m S z := by
    intro m S z hz
    rw [huseqS m]
    exact (hstep m (useq m) (hGood m)).2 S z hz
  have hStab : ∀ j k : ℕ, j ≤ k → ∀ (S : Finset (Fin n)), ∀ z ∈ E j, useq k S z = useq j S z := by
    intro j k hjk
    induction k with
    | zero =>
        have hj : j = 0 := Nat.le_zero.1 hjk
        subst hj
        exact fun S z _ => rfl
    | succ l ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hjk) with h | h
        · have hjl : j ≤ l := Nat.lt_succ_iff.1 h
          intro S z hz
          rw [hLink l S z (hEmono' j l hjl hz)]
          exact ih hjl S z hz
        · subst h
          exact fun S z _ => rfl
  set idx : (Fin n → ℂ) → ℕ := fun z => if h : ∃ m : ℕ, z ∈ E m then Nat.find h else 0 with hidx
  have hidxmem : ∀ z ∈ X, z ∈ E (idx z) := by
    intro z hz
    have h : ∃ m : ℕ, z ∈ E m := hEcover z hz
    simp only [hidx, dif_pos h]
    exact Nat.find_spec h
  have hidxle : ∀ (m : ℕ) (z : Fin n → ℂ), z ∈ E m → idx z ≤ m := by
    intro m z hz
    have h : ∃ m : ℕ, z ∈ E m := ⟨m, hz⟩
    simp only [hidx, dif_pos h]
    exact Nat.find_min' h hz
  refine ⟨fun S z => useq (idx z) S z, ?_, ?_, ?_⟩
  · intro S z hz
    obtain ⟨m, hm⟩ := hEcover z hz
    refine ((hGood m).1 S).contDiffAt.congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem ((hEopen m).mem_nhds hm) fun y hy => ?_
    exact (hStab (idx y) m (hidxle m y hy) S y (hidxmem y (hEsub m hy))).symm
  · intro S hS z
    exact (hGood (idx z)).2.1 S hS z
  · intro S z hz
    obtain ⟨m, hm⟩ := hEcover z hz
    have hloc : setDbar (fun S z => useq (idx z) S z) S z = setDbar (useq m) S z := by
      refine setDbar_congr_on_isOpen (hEopen m) (fun T y hy => ?_) hm S
      exact (hStab (idx y) m (hidxle m y hy) T y (hidxmem y (hEsub m hy))).symm
    rw [hloc]
    exact (hGood m).2.2 S z (hEmono m hm)

end Exhaustion

section GlobalInstance

variable {n : ℕ}

/-- The exhaustion of `ℂ^n` by concentric polydiscs. -/
def polydiscExhaustion (n : ℕ) (m : ℕ) : Set (Fin n → ℂ) :=
  polydisc (fun _ => 0) fun _ => (m : ℝ) + 1

theorem isOpen_polydiscExhaustion (n m : ℕ) : IsOpen (polydiscExhaustion n m) :=
  isOpen_polydisc _ _

theorem polydiscExhaustion_mono (n m : ℕ) :
    polydiscExhaustion n m ⊆ polydiscExhaustion n (m + 1) := by
  intro z hz i
  refine Metric.ball_subset_ball ?_ (hz i)
  push_cast
  linarith

theorem mem_polydiscExhaustion (z : Fin n → ℂ) : ∃ m : ℕ, z ∈ polydiscExhaustion n m := by
  obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
  refine ⟨m, fun i => ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_trans (lt_of_le_of_lt (norm_le_pi_norm z i) hm) (by linarith)

/-- The Dolbeault system is solvable from one polydisc of the exhaustion to the previous one. -/
theorem dbarStageSolvable_polydiscExhaustion :
    DbarStageSolvable (polydiscExhaustion n) Set.univ := by
  intro m q g hCgOn hdg hgclosed
  have hCg : SmoothSetForm g := fun S =>
    contDiff_iff_contDiffAt.2 fun z => hCgOn S z (Set.mem_univ z)
  have hρ : ∀ _ : Fin n, (0 : ℝ) < (m : ℝ) + 1 := fun _ => by positivity
  have hρr : ∀ _ : Fin n, ((m : ℝ) + 1) < (m : ℝ) + 2 := fun _ => by linarith
  have hsub : polydisc (fun _ : Fin n => (0 : ℂ)) (fun _ => (m : ℝ) + 2)
      ⊆ polydiscExhaustion n (m + 1) := by
    intro z hz i
    refine Metric.ball_subset_ball ?_ (hz i)
    push_cast
    linarith
  obtain ⟨w, hCw, hdw, hweq⟩ :=
    setDbar_polydisc_solve (c := fun _ : Fin n => (0 : ℂ)) (ρ := fun _ => (m : ℝ) + 1)
      (r := fun _ => (m : ℝ) + 2) hρ hρr hCg (hdg.empty (Nat.succ_ne_zero q)) hdg
      (fun S z hz => hgclosed S z (hsub hz))
  exact ⟨w, hCw, hdw, hweq⟩

/-- **The Dolbeault system in degree at least two is globally solvable on `ℂ^n`.** -/
theorem setDbar_global_solve {q : ℕ} {f : SetForm n} (hCf : SmoothSetForm f)
    (hdeg : SetFormDeg (q + 2) f)
    (hclosed : ∀ (S : Finset (Fin n)) (z : Fin n → ℂ), setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg (q + 1) u ∧
      ∀ (S : Finset (Fin n)) (z : Fin n → ℂ), setDbar u S z = f S z := by
  obtain ⟨u, hCu, hdu, hueq⟩ :=
    setDbar_exhaustion_solve (E := polydiscExhaustion n) (isOpen_polydiscExhaustion n)
      (polydiscExhaustion_mono n) dbarStageSolvable_polydiscExhaustion
      (X := Set.univ) (fun _ => Set.subset_univ _)
      (fun z _ => mem_polydiscExhaustion z) (hCf.smoothOn Set.univ) hdeg
      (fun S z _ => hclosed S z)
  refine ⟨u, fun S => contDiff_iff_contDiffAt.2 fun z => hCu S z (Set.mem_univ z), hdu,
    fun S z => hueq S z (Set.mem_univ z)⟩

end GlobalInstance

section PuncturedInstance

variable {n : ℕ}

theorem isOpen_puncturedExhaustion (n m : ℕ) : IsOpen (puncturedExhaustion n m) :=
  isOpen_productDomain fun _ => isOpen_annulus _ _

theorem puncturedExhaustion_subset (n m : ℕ) : puncturedExhaustion n m ⊆ puncturedSpace n := by
  intro z hz i
  have h := (hz i).1
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  exact norm_ne_zero_iff.1 (ne_of_gt (lt_trans hpos h))

/-- The Dolbeault system is solvable from one polyannulus of the exhaustion to the previous one. -/
theorem dbarStageSolvable_puncturedExhaustion :
    DbarStageSolvable (puncturedExhaustion n) (puncturedSpace n) := by
  intro m q g hCgOn hdg hgclosed
  have ha : ∀ _ : Fin n, (0 : ℝ) ≤ 1 / ((m : ℝ) + 3) := fun _ => by positivity
  have haa' : ∀ _ : Fin n, 1 / ((m : ℝ) + 3) < 1 / ((m : ℝ) + 2) := fun _ => by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have ha'b' : ∀ _ : Fin n, 1 / ((m : ℝ) + 2) < (m : ℝ) + 2 := fun _ => by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hb'b : ∀ _ : Fin n, ((m : ℝ) + 2) < (m : ℝ) + 3 := fun _ => by linarith
  set K : Set (Fin n → ℂ) :=
    closedPolyannulus (fun _ : Fin n => 1 / ((m : ℝ) + 3)) (fun _ : Fin n => (m : ℝ) + 3) with hK
  have hKsub : K ⊆ puncturedSpace n := by
    intro z hz i hcon
    have h := (hz i).1
    rw [hcon, norm_zero] at h
    have : (0 : ℝ) < 1 / ((m : ℝ) + 3) := by positivity
    linarith
  obtain ⟨G, V, hVopen, hKV, hCG, hGeq, hGzero⟩ :=
    exists_contDiff_family_eqOn (h := g) (K := K) (W := puncturedSpace n)
      (isCompact_closedPolyannulus _ _) isOpen_puncturedSpace hKsub hCgOn
  have hGdeg : SetFormDeg (q + 1) G := fun S hS z => hGzero S z (hdg S hS z)
  have hGloc : ∀ (S : Finset (Fin n)), ∀ z ∈ V, setDbar G S z = setDbar g S z := by
    intro S z hz
    exact setDbar_congr_on_isOpen hVopen (fun T y hy => hGeq T y hy) hz S
  have hannK : ∀ z ∈ productDomain (fun _ : Fin n => annulus (1 / ((m : ℝ) + 3)) ((m : ℝ) + 3)),
      z ∈ K := fun z hz i => ⟨(hz i).1.le, (hz i).2.le⟩
  have hcast : ∀ z : Fin n → ℂ,
      z ∈ productDomain (fun _ : Fin n => annulus (1 / ((m : ℝ) + 3)) ((m : ℝ) + 3)) →
      z ∈ puncturedExhaustion n (m + 1) := by
    intro z hz i
    have h1 : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 3 := by push_cast; ring
    rw [h1]
    exact hz i
  obtain ⟨w, hCw, hdw, hweq⟩ :=
    setDbar_polyannulus_solve (a := fun _ => 1 / ((m : ℝ) + 3)) (a' := fun _ => 1 / ((m : ℝ) + 2))
      (b' := fun _ => (m : ℝ) + 2) (b := fun _ => (m : ℝ) + 3)
      ha haa' ha'b' hb'b hCG (hGdeg.empty (Nat.succ_ne_zero q)) hGdeg
      (fun S z hz => by
        rw [hGloc S z (hKV (hannK z hz))]
        exact hgclosed S z (hcast z hz))
  refine ⟨w, hCw, hdw, fun S z hz => ?_⟩
  have hzK : z ∈ K := by
    refine fun i => ⟨?_, ?_⟩
    · refine le_trans ?_ (hz i).1.le
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    · exact le_trans (hz i).2.le (by linarith)
  rw [hweq S z hz]
  exact hGeq S z (hKV hzK)

/-- **The Dolbeault system in degree at least two is globally solvable on `(ℂ^×)^n`.** -/
theorem setDbar_punctured_solve {q : ℕ} {f : SetForm n}
    (hCf : SmoothSetFormOn f (puncturedSpace n)) (hdeg : SetFormDeg (q + 2) f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ puncturedSpace n, setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetFormOn u (puncturedSpace n) ∧ SetFormDeg (q + 1) u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ puncturedSpace n, setDbar u S z = f S z :=
  setDbar_exhaustion_solve (E := puncturedExhaustion n) (isOpen_puncturedExhaustion n)
    (puncturedExhaustion_mono n) dbarStageSolvable_puncturedExhaustion
    (puncturedExhaustion_subset n) (fun _ hz => mem_puncturedExhaustion_of_mem hz) hCf hdeg hclosed

end PuncturedInstance


section DegreeOne

variable {n : ℕ}

/-- The set-indexed form of degree zero attached to a function: it is the function at the empty set
of directions and zero elsewhere. -/
def pointForm (u₀ : (Fin n → ℂ) → ℂ) : SetForm n := fun S z => if S = ∅ then u₀ z else 0

@[simp] theorem pointForm_empty (u₀ : (Fin n → ℂ) → ℂ) :
    pointForm u₀ (∅ : Finset (Fin n)) = u₀ := by
  funext y
  simp [pointForm]

theorem pointForm_of_ne (u₀ : (Fin n → ℂ) → ℂ) {S : Finset (Fin n)} (hS : S ≠ ∅) :
    pointForm u₀ S = fun _ : Fin n → ℂ => (0 : ℂ) := by
  funext y
  simp [pointForm, hS]

theorem smoothSetForm_pointForm {u₀ : (Fin n → ℂ) → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₀) : SmoothSetForm (pointForm u₀) := by
  intro S
  by_cases hS : S = ∅
  · rw [hS, pointForm_empty]
    exact h
  · rw [pointForm_of_ne u₀ hS]
    exact contDiff_const

theorem setFormDeg_pointForm (u₀ : (Fin n → ℂ) → ℂ) : SetFormDeg 0 (pointForm u₀) := by
  intro S hS z
  have hne : S ≠ ∅ := fun h => hS (by rw [h, Finset.card_empty])
  simp [pointForm, hne]

/-- On a single direction the differential of a degree-zero form is the antiholomorphic derivative
of its coefficient. -/
theorem setDbar_pointForm_singleton (u₀ : (Fin n → ℂ) → ℂ) (k : Fin n) (z : Fin n → ℂ) :
    setDbar (pointForm u₀) {k} z = dzbarAt u₀ k z := by
  show (∑ j ∈ ({k} : Finset (Fin n)),
    insertSign j (({k} : Finset (Fin n)).erase j) *
      dzbarAt (pointForm u₀ (({k} : Finset (Fin n)).erase j)) j z) = _
  rw [Finset.sum_singleton, Finset.erase_singleton]
  have hsign : insertSign k (∅ : Finset (Fin n)) = 1 := by
    show (-1 : ℂ) ^ ((∅ : Finset (Fin n)).filter (fun j => j < k)).card = 1
    rw [Finset.filter_empty, Finset.card_empty, pow_zero]
  rw [hsign, pointForm_empty, one_mul]

/-- The differential of a degree-zero form vanishes outside the sets of one direction. -/
theorem setDbar_pointForm_of_card_ne_one (u₀ : (Fin n → ℂ) → ℂ) {S : Finset (Fin n)}
    (hS : S.card ≠ 1) (z : Fin n → ℂ) : setDbar (pointForm u₀) S z = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have hcard : 1 ≤ S.card := Finset.card_pos.2 ⟨k, hk⟩
  have hge : 2 ≤ S.card := by omega
  have hne : S.erase k ≠ ∅ := by
    intro h
    have := Finset.card_erase_of_mem hk
    rw [h, Finset.card_empty] at this
    omega
  rw [pointForm_of_ne u₀ hne, dzbarAt_zero, mul_zero]

/-- The compatibility of the coefficients of a `∂̄`-closed form of degree one. -/
theorem dzbarAt_comm_of_setDbar_zero {f : SetForm n} {P : Set (Fin n → ℂ)}
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ P, setDbar f S z = 0) (j k : Fin n) :
    ∀ z ∈ P, dzbarAt (f {j}) k z = dzbarAt (f {k}) j z := by
  intro z hz
  rcases eq_or_ne j k with rfl | hjk
  · rfl
  · rcases lt_or_gt_of_ne hjk with h | h
    · have hpair : ({j, k} : Finset (Fin n)).erase j = {k} := by
        rw [Finset.erase_insert (by simpa using hjk)]
      have hpair' : ({j, k} : Finset (Fin n)).erase k = {j} := by
        rw [Finset.pair_comm, Finset.erase_insert (by simpa using hjk.symm)]
      have hsum := hclosed {j, k} z hz
      rw [show setDbar f {j, k} z = ∑ i ∈ ({j, k} : Finset (Fin n)),
          insertSign i (({j, k} : Finset (Fin n)).erase i) *
            dzbarAt (f (({j, k} : Finset (Fin n)).erase i)) i z from rfl,
        Finset.sum_pair hjk, hpair, hpair'] at hsum
      have hsj : insertSign j ({k} : Finset (Fin n)) = 1 := by
        show (-1 : ℂ) ^ (({k} : Finset (Fin n)).filter (fun i => i < j)).card = 1
        rw [Finset.filter_singleton, if_neg (by exact not_lt_of_gt h), Finset.card_empty, pow_zero]
      have hsk : insertSign k ({j} : Finset (Fin n)) = -1 := by
        show (-1 : ℂ) ^ (({j} : Finset (Fin n)).filter (fun i => i < k)).card = -1
        rw [Finset.filter_singleton, if_pos h, Finset.card_singleton, pow_one]
      rw [hsj, hsk, one_mul] at hsum
      linear_combination -hsum
    · have hpair : ({k, j} : Finset (Fin n)).erase k = {j} := by
        rw [Finset.erase_insert (by simpa using hjk.symm)]
      have hpair' : ({k, j} : Finset (Fin n)).erase j = {k} := by
        rw [Finset.pair_comm, Finset.erase_insert (by simpa using hjk)]
      have hsum := hclosed {k, j} z hz
      rw [show setDbar f {k, j} z = ∑ i ∈ ({k, j} : Finset (Fin n)),
          insertSign i (({k, j} : Finset (Fin n)).erase i) *
            dzbarAt (f (({k, j} : Finset (Fin n)).erase i)) i z from rfl,
        Finset.sum_pair hjk.symm, hpair, hpair'] at hsum
      have hsk : insertSign k ({j} : Finset (Fin n)) = 1 := by
        show (-1 : ℂ) ^ (({j} : Finset (Fin n)).filter (fun i => i < k)).card = 1
        rw [Finset.filter_singleton, if_neg (by exact not_lt_of_gt h), Finset.card_empty, pow_zero]
      have hsj : insertSign j ({k} : Finset (Fin n)) = -1 := by
        show (-1 : ℂ) ^ (({k} : Finset (Fin n)).filter (fun i => i < j)).card = -1
        rw [Finset.filter_singleton, if_pos h, Finset.card_singleton, pow_one]
      rw [hsj, hsk, one_mul] at hsum
      linear_combination hsum

/-- **A `∂̄`-closed form of degree one on `ℂ^n` is exact.** -/
theorem setDbar_global_solve_one {f : SetForm n} (hCf : SmoothSetForm f) (hdeg : SetFormDeg 1 f)
    (hclosed : ∀ (S : Finset (Fin n)) (z : Fin n → ℂ), setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg 0 u ∧
      ∀ (S : Finset (Fin n)) (z : Fin n → ℂ), setDbar u S z = f S z := by
  obtain ⟨u₀, hCu₀, hu₀⟩ :=
    dbar_global_solve (f := fun k => f {k}) (fun k => hCf _)
      (fun j k z => dzbarAt_comm_of_setDbar_zero (P := Set.univ)
        (fun S y _ => hclosed S y) j k z (Set.mem_univ z))
  refine ⟨pointForm u₀, smoothSetForm_pointForm hCu₀, setFormDeg_pointForm u₀, fun S z => ?_⟩
  by_cases hS : S.card = 1
  · obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hS
    subst hk
    rw [setDbar_pointForm_singleton, hu₀ k z]
  · rw [setDbar_pointForm_of_card_ne_one u₀ hS z, hdeg S hS z]

/-- **A `∂̄`-closed form of degree one on `(ℂ^×)^n` is exact.** -/
theorem setDbar_punctured_solve_one {f : SetForm n}
    (hCf : SmoothSetFormOn f (puncturedSpace n)) (hdeg : SetFormDeg 1 f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ puncturedSpace n, setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetFormOn u (puncturedSpace n) ∧ SetFormDeg 0 u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ puncturedSpace n, setDbar u S z = f S z := by
  obtain ⟨u₀, hCu₀, hu₀⟩ :=
    dbar_punctured_solve (f := fun k => f {k}) (fun k z hz => hCf {k} z hz)
      (fun j k z hz => dzbarAt_comm_of_setDbar_zero hclosed j k z hz)
  refine ⟨pointForm u₀, ?_, setFormDeg_pointForm u₀, fun S z hz => ?_⟩
  · intro S z hz
    by_cases hS : S = ∅
    · rw [hS, pointForm_empty]
      exact hCu₀ z hz
    · rw [pointForm_of_ne u₀ hS]
      exact contDiffAt_const
  · by_cases hS : S.card = 1
    · obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hS
      subst hk
      rw [setDbar_pointForm_singleton, hu₀ k z hz]
    · rw [setDbar_pointForm_of_card_ne_one u₀ hS z, hdeg S hS z]

end DegreeOne

section Capstone

variable {n : ℕ}

/-- **Exactness of the Dolbeault complex on `ℂ^n` in every positive degree.** -/
theorem setDbar_exact_global {q : ℕ} {f : SetForm n} (hCf : SmoothSetForm f)
    (hdeg : SetFormDeg (q + 1) f)
    (hclosed : ∀ (S : Finset (Fin n)) (z : Fin n → ℂ), setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetForm u ∧ SetFormDeg q u ∧
      ∀ (S : Finset (Fin n)) (z : Fin n → ℂ), setDbar u S z = f S z := by
  cases q with
  | zero => exact setDbar_global_solve_one hCf hdeg hclosed
  | succ j => exact setDbar_global_solve hCf hdeg hclosed

/-- **Exactness of the Dolbeault complex on `(ℂ^×)^n` in every positive degree.** -/
theorem setDbar_exact_punctured {q : ℕ} {f : SetForm n}
    (hCf : SmoothSetFormOn f (puncturedSpace n)) (hdeg : SetFormDeg (q + 1) f)
    (hclosed : ∀ S : Finset (Fin n), ∀ z ∈ puncturedSpace n, setDbar f S z = 0) :
    ∃ u : SetForm n, SmoothSetFormOn u (puncturedSpace n) ∧ SetFormDeg q u ∧
      ∀ S : Finset (Fin n), ∀ z ∈ puncturedSpace n, setDbar u S z = f S z := by
  cases q with
  | zero => exact setDbar_punctured_solve_one hCf hdeg hclosed
  | succ j => exact setDbar_punctured_solve hCf hdeg hclosed

end Capstone

end HTGeometry
