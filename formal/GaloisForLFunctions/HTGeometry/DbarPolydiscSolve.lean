import GaloisForLFunctions.HTGeometry.DbarSeveral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The Dolbeault–Grothendieck lemma on a polydisc

The induction step of `DbarSeveral` needs two cutoffs: one in the distinguished coordinate, equal
to one on the smaller disc and supported in the larger, and one in all coordinates, equal to one on
the whole polydisc and compactly supported.  Both are bump functions, and the second exists because
a polydisc is bounded in the supremum norm of the coordinate space.

The `∂̄` of a smooth function is smooth, because it is a fixed continuous linear functional of the
differential.  That is what lets the induction step be iterated: the residue of a smooth datum
after one step is again smooth.

The induction clears the directions of the datum from the top down.  Each step shrinks the
polydisc once, so after `n` steps the solution lives on any prescribed polydisc strictly inside the
original — which is the local statement the Dolbeault–Grothendieck lemma asserts.

* `HTGeometry.contDiff_infty_dzbarAt` : `∂̄_j` preserves smoothness.
* `HTGeometry.exists_polydisc_bumps` : the two cutoffs.
* `HTGeometry.dbar_polydisc_solve_aux` : the induction, clearing directions above an index.
* `HTGeometry.dbar_polydisc_solve` : **the Dolbeault–Grothendieck lemma on a polydisc.**
-/

namespace HTGeometry

open Complex

section Smoothness

variable {n : ℕ}

/-- **`∂̄_j` preserves smoothness.**  It is a fixed continuous linear functional of the
differential. -/
theorem contDiff_infty_dzbarAt {G : (Fin n → ℂ) → ℂ}
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dzbarAt G j) := by
  have hd : Differentiable ℝ G := (contDiff_infty_iff_fderiv.mp hC).1
  have heq : dzbarAt G j = fun z => dzbarFunctional j (fderiv ℝ G z) := by
    funext z
    exact dzbarAt_eq_functional hd j z
  rw [heq]
  exact (dzbarFunctional j).contDiff.comp (contDiff_infty_iff_fderiv.mp hC).2

end Smoothness

section Bumps

variable {n : ℕ}

/-- **The two cutoffs of the induction step.**  A bump in the `k`-th coordinate, one on the small
disc and supported in the large one, and a bump in all coordinates, one on the whole polydisc and
compactly supported. -/
theorem exists_polydisc_bumps {c : Fin n → ℂ} {r r' : Fin n → ℝ} {R : ℝ} (k : Fin n)
    (hr'pos : 0 < r' k) (hlt : r' k < r k) (hRpos : 0 < R) (hR : ∀ i, r i ≤ R) :
    ∃ (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi ∧
      HasCompactSupport psi ∧
      (∀ t : ℂ, chi t ≠ 0 → t ∈ Metric.ball (c k) (r k)) ∧
      (∀ z ∈ polydisc c r', chi (z k) = 1) ∧
      (∀ z ∈ polydisc c r, psi z = 1) := by
  let bx : ContDiffBump (c k) := ⟨r' k, r k, hr'pos, hlt⟩
  let bp : ContDiffBump c := ⟨R, R + 1, hRpos, by linarith⟩
  refine ⟨(bx : ℂ → ℝ), (bp : (Fin n → ℂ) → ℝ), bx.contDiff, bp.contDiff,
    bp.hasCompactSupport, ?_, ?_, ?_⟩
  · intro t ht
    have hsupp : t ∈ Function.support (bx : ℂ → ℝ) := ht
    rw [bx.support_eq] at hsupp
    exact hsupp
  · intro z hz
    exact bx.one_of_mem_closedBall (Metric.ball_subset_closedBall (hz k))
  · intro z hz
    refine bp.one_of_mem_closedBall ?_
    refine Metric.mem_closedBall.mpr ?_
    refine (dist_pi_le_iff hRpos.le).mpr fun i => ?_
    exact le_trans (le_of_lt (Metric.mem_ball.mp (hz i))) (hR i)

end Bumps

section Recursion

variable {n : ℕ}

/-- **The Dolbeault induction**, clearing the directions of the datum from the index `m` upwards.
Each step solves in one direction and shrinks the polydisc once; the residue is again smooth and
`∂̄`-closed, because `∂̄` preserves smoothness and the antiholomorphic derivatives commute. -/
theorem dbar_polydisc_solve_aux (c : Fin n → ℂ) (R : ℝ) (hRpos : 0 < R) :
    ∀ m : ℕ, ∀ (f : Fin n → (Fin n → ℂ) → ℂ) (r ρ : Fin n → ℝ),
      (∀ i, 0 < ρ i) → (∀ i, ρ i < r i) → (∀ i, r i ≤ R) →
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j)) →
      (∀ j j' : Fin n, ∀ z ∈ polydisc c r, dzbarAt (f j) j' z = dzbarAt (f j') j z) →
      (∀ j : Fin n, m ≤ (j : ℕ) → ∀ z ∈ polydisc c r, f j z = 0) →
      ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
        ∀ j : Fin n, ∀ z ∈ polydisc c ρ, dzbarAt u j z = f j z := by
  intro m
  induction m with
  | zero =>
      intro f r ρ hρ hρr hrR hCf hclosed hvan
      refine ⟨fun _ => 0, contDiff_const, fun j z hz => ?_⟩
      rw [dzbarAt_zero]
      exact (hvan j (Nat.zero_le _) z (polydisc_mono (fun i => (hρr i).le) hz)).symm
  | succ m ih =>
      intro f r ρ hρ hρr hrR hCf hclosed hvan
      by_cases hmn : n ≤ m
      · refine ih f r ρ hρ hρr hrR hCf hclosed fun j hj => ?_
        exact absurd hj (by have := j.isLt; omega)
      · push_neg at hmn
        set k : Fin n := ⟨m, hmn⟩ with hk
        set r'' : Fin n → ℝ := fun i => (ρ i + r i) / 2 with hr''def
        have hρr'' : ∀ i, ρ i < r'' i := fun i => by
          have := hρr i; simp only [hr''def]; linarith
        have hr''r : ∀ i, r'' i < r i := fun i => by
          have := hρr i; simp only [hr''def]; linarith
        have hr''pos : ∀ i, 0 < r'' i := fun i => lt_trans (hρ i) (hρr'' i)
        have hr''R : ∀ i, r'' i ≤ R := fun i => le_trans (hr''r i).le (hrR i)
        have hsub : polydisc c r'' ⊆ polydisc c r := polydisc_mono fun i => (hr''r i).le
        obtain ⟨chi, psi, hCchi, hCpsi, hcspsi, hchi, hchione, hpsione⟩ :=
          exists_polydisc_bumps (c := c) (r := r) (r' := r'') (R := R) k
            (hr''pos k) (hr''r k) hRpos hrR
        have hCG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)) :=
          (hCchi.comp (contDiff_apply ℝ ℂ k)).smul (hCpsi.smul (hCf k))
        have hcs : HasCompactSupport
            (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)) := by
          refine hcspsi.mono fun x hx => ?_
          by_contra hzero
          simp only [Function.mem_support, not_not] at hzero
          exact hx (by simp [hzero])
        obtain ⟨U, hCU, hUk, hUj⟩ :=
          dbar_polydisc_step_smooth (f := f) (c := c) (r := r) (r' := r'') (k := k)
            (fun i => (hr''r i).le) chi psi hchi hchione hpsione hCG hcs
            (fun j z hz => hclosed k j z hz)
        have hdU : Differentiable ℝ U := (contDiff_infty_iff_fderiv.mp hCU).1
        have h2top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
        have hCU2 : ContDiff ℝ 2 U := hCU.of_le h2top
        have hCdU : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dzbarAt U j) :=
          fun j => contDiff_infty_dzbarAt hCU j
        have hddU : ∀ j : Fin n, Differentiable ℝ (dzbarAt U j) :=
          fun j => (contDiff_infty_iff_fderiv.mp (hCdU j)).1
        have hdf : ∀ j : Fin n, Differentiable ℝ (f j) :=
          fun j => (contDiff_infty_iff_fderiv.mp (hCf j)).1
        set g : Fin n → (Fin n → ℂ) → ℂ := fun j z => f j z - dzbarAt U j z with hgdef
        have hCg : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g j) :=
          fun j => (hCf j).sub (hCdU j)
        have hclosedg : ∀ j j' : Fin n, ∀ z ∈ polydisc c r'',
            dzbarAt (g j) j' z = dzbarAt (g j') j z := by
          intro j j' z hz
          have h1 : dzbarAt (g j) j' z = dzbarAt (f j) j' z - dzbarAt (dzbarAt U j) j' z :=
            dzbarAt_sub (hdf j) (hddU j) j' z
          have h2 : dzbarAt (g j') j z = dzbarAt (f j') j z - dzbarAt (dzbarAt U j') j z :=
            dzbarAt_sub (hdf j') (hddU j') j z
          rw [h1, h2, hclosed j j' z (hsub hz), dzbarAt_comm hCU2 j' j z]
        have hvang : ∀ j : Fin n, m ≤ (j : ℕ) → ∀ z ∈ polydisc c r'', g j z = 0 := by
          intro j hj z hz
          rcases eq_or_lt_of_le hj with heq | hlt
          · have hjk : j = k := Fin.ext heq.symm
            subst hjk
            show f k z - dzbarAt U k z = 0
            rw [hUk z hz]
            ring
          · have hjne : j ≠ k := by
              intro h
              rw [h] at hlt
              exact absurd hlt (by simp [hk])
            have hfj : ∀ y ∈ polydisc c r, f j y = 0 := hvan j (by omega)
            show f j z - dzbarAt U j z = 0
            rw [hfj z (hsub hz), hUj j hjne hfj z hz]
            ring
        obtain ⟨v, hCv, hv⟩ := ih g r'' ρ hρ hρr'' hr''R hCg hclosedg hvang
        have hdv : Differentiable ℝ v := (contDiff_infty_iff_fderiv.mp hCv).1
        refine ⟨fun x => U x + v x, hCU.add hCv, ?_⟩
        refine dzbarAt_add_solution hdU hdv ?_
        intro j z hz
        exact hv j z hz

/-- **The Dolbeault–Grothendieck lemma on a polydisc.**  A smooth `∂̄`-closed datum on a polydisc has
a smooth primitive on every strictly smaller polydisc. -/
theorem dbar_polydisc_solve {c : Fin n → ℂ} {r ρ : Fin n → ℝ}
    (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, ρ i < r i)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ j j' : Fin n, ∀ z ∈ polydisc c r, dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      ∀ j : Fin n, ∀ z ∈ polydisc c ρ, dzbarAt u j z = f j z := by
  classical
  refine dbar_polydisc_solve_aux c (1 + ∑ i, |r i|) (by positivity) n f r ρ hρ hρr
    (fun i => ?_) hCf hclosed (fun j hj => absurd hj (by have := j.isLt; omega))
  have h1 : |r i| ≤ ∑ i', |r i'| :=
    Finset.single_le_sum (f := fun i' => |r i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : r i ≤ |r i| := le_abs_self _
  linarith

end Recursion

end HTGeometry
