import GaloisForLFunctions.HTGeometry.PolyannulusRunge
import GaloisForLFunctions.HTGeometry.DbarGlobalSolve

/-!
# Solving `∂̄` on a product of punctured planes

`(ℂ^×)^n` is exhausted by polyannuli, and on each of them the Dolbeault–Grothendieck lemma solves
the system.  Consecutive solutions differ by a function holomorphic on the smaller polyannulus, and
the Runge theorem on a polyannulus corrects that difference by a function holomorphic on the whole
of `(ℂ^×)^n`, to any accuracy.  The corrected sequence then converges locally uniformly and its
limit solves the system everywhere, exactly as over `ℂⁿ`.

* `HTGeometry.puncturedSpace` : the product of punctured planes.
* `HTGeometry.exists_polyannulus_cutoff` : a smooth cutoff between two nested polyannuli.
* `HTGeometry.puncturedExhaustion` : the exhausting polyannuli.
-/

namespace HTGeometry

open Complex GaloisForLFunctions.HTGeometry

section PuncturedSpace

variable {n : ℕ}

/-- The product of punctured planes. -/
def puncturedSpace (n : ℕ) : Set (Fin n → ℂ) := productDomain fun _ : Fin n => {w : ℂ | w ≠ 0}

theorem mem_puncturedSpace {z : Fin n → ℂ} : z ∈ puncturedSpace n ↔ ∀ i, z i ≠ 0 := Iff.rfl

theorem isOpen_puncturedSpace : IsOpen (puncturedSpace n) :=
  isOpen_productDomain fun _ => isOpen_ne

/-- The exhausting polyannuli of the punctured space. -/
def puncturedExhaustion (n : ℕ) (m : ℕ) : Set (Fin n → ℂ) :=
  productDomain fun _ : Fin n => annulus (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2)

theorem annulus_mono_pair {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    annulus a' b' ⊆ annulus a b := annulus_mono ha hb

/-- The exhaustion increases. -/
theorem puncturedExhaustion_mono (n m : ℕ) :
    puncturedExhaustion n m ⊆ puncturedExhaustion n (m + 1) := by
  intro z hz i
  refine annulus_mono ?_ ?_ (hz i)
  · push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · push_cast
    linarith

/-- The exhaustion fills the punctured space. -/
theorem mem_puncturedExhaustion_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedSpace n) :
    ∃ m : ℕ, z ∈ puncturedExhaustion n m := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨0, fun i => absurd i.isLt (by omega)⟩
  · have hpos : ∀ i, 0 < ‖z i‖ := fun i => norm_pos_iff.2 (hz i)
    obtain ⟨m₁, hm₁⟩ := exists_nat_gt (‖z‖)
    obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℕ, ∀ i, (‖z i‖)⁻¹ < (m₂ : ℝ) := by
      obtain ⟨B, hB⟩ := (Set.finite_range fun i => (‖z i‖)⁻¹).bddAbove
      obtain ⟨m₂, hm₂⟩ := exists_nat_gt B
      exact ⟨m₂, fun i => lt_of_le_of_lt (hB (Set.mem_range_self i)) hm₂⟩
    refine ⟨max m₁ m₂, fun i => ?_⟩
    have hzi : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
    constructor
    · rw [div_lt_iff₀ (by positivity)]
      have h1 : (‖z i‖)⁻¹ < (m₂ : ℝ) := hm₂ i
      have h2 : (m₂ : ℝ) ≤ (max m₁ m₂ : ℕ) := by exact_mod_cast le_max_right m₁ m₂
      have h3 : (‖z i‖)⁻¹ < ((max m₁ m₂ : ℕ) : ℝ) + 2 := by linarith
      rw [inv_lt_iff_one_lt_mul₀ (hpos i)] at h3
      linarith
    · have h1 : ‖z i‖ < (m₁ : ℝ) := lt_of_le_of_lt hzi hm₁
      have h2 : (m₁ : ℝ) ≤ (max m₁ m₂ : ℕ) := by exact_mod_cast le_max_left m₁ m₂
      linarith

end PuncturedSpace

section Cutoff

variable {n : ℕ}

/-- **A smooth cutoff between two nested polyannuli**: one on the inner one, supported in the outer
one.  It is the product of the coordinate annulus cutoffs, so it is compactly supported inside the
punctured space. -/
theorem exists_polyannulus_cutoff {a a' b' b : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (haa' : ∀ i, a i < a' i) (ha'b' : ∀ i, a' i < b' i) (hb'b : ∀ i, b' i < b i) :
    ∃ ψ : (Fin n → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ z : Fin n → ℂ, ψ z ≠ 0 → z ∈ productDomain fun i => annulus (a i) (b i)) ∧
      (∀ z ∈ productDomain fun i => annulus (a' i) (b' i), ψ z = 1) := by
  classical
  have hchi : ∀ i : Fin n, ∃ chi : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi ∧
      (∀ t : ℂ, chi t ≠ 0 → t ∈ annulus (a i) (b i)) ∧
      (∀ t ∈ annulus (a' i) (b' i), chi t = 1) := fun i =>
    exists_annulus_cutoff (ha i) (haa' i) (ha'b' i) (hb'b i)
  choose chi hCchi hchisupp hchione using hchi
  refine ⟨fun z => ∏ i, chi i (z i), ?_, ?_, ?_⟩
  · have heq : (fun z : Fin n → ℂ => ∏ i, chi i (z i))
        = ∏ i ∈ Finset.univ, fun z : Fin n → ℂ => chi i (z i) := by
      funext z
      simp [Finset.prod_apply]
    rw [heq]
    exact Finset.prod_induction _ (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun p q hp hq => hp.mul hq) contDiff_const
      (fun i _ => (hCchi i).comp (contDiff_apply ℝ ℂ i))
  · intro z hz i
    refine hchisupp i (z i) ?_
    intro hcon
    refine hz ?_
    exact Finset.prod_eq_zero (Finset.mem_univ i) hcon
  · intro z hz
    refine Finset.prod_eq_one fun i _ => ?_
    exact hchione i (z i) (hz i)

end Cutoff

section LocalSub

variable {n : ℕ}

/-- The antiholomorphic Wirtinger part is additive. -/
theorem wirtingerAntihol_sub (A B : ℂ →L[ℝ] ℂ) :
    wirtingerAntihol (A - B) = wirtingerAntihol A - wirtingerAntihol B := by
  simp only [wirtingerAntihol, ContinuousLinearMap.sub_apply]
  ring

/-- **`∂̄_j` is subtractive at a point of differentiability.** -/
theorem dzbarAt_sub_at {F G : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (j : Fin n) :
    dzbarAt (fun x => F x - G x) j z = dzbarAt F j z - dzbarAt G j z := by
  have hembed : DifferentiableAt ℝ (fun s : ℂ => Function.update z j s) (z j) :=
    ((contDiff_updateEmbed j z).differentiable (by norm_num)).differentiableAt
  have hupd : Function.update z j (z j) = z := Function.update_eq_self j z
  have hFs : DifferentiableAt ℝ (dbarSlice F j z) (z j) := by
    refine DifferentiableAt.comp (z j) ?_ hembed
    rw [hupd]
    exact hF
  have hGs : DifferentiableAt ℝ (dbarSlice G j z) (z j) := by
    refine DifferentiableAt.comp (z j) ?_ hembed
    rw [hupd]
    exact hG
  have hslice : dbarSlice (fun x => F x - G x) j z
      = fun t => dbarSlice F j z t - dbarSlice G j z t := rfl
  have hfd : fderiv ℝ (fun t : ℂ => dbarSlice F j z t - dbarSlice G j z t) (z j)
      = fderiv ℝ (dbarSlice F j z) (z j) - fderiv ℝ (dbarSlice G j z) (z j) :=
    fderiv_sub hFs hGs
  rw [dzbarAt, hslice, dzbarAt, dzbarAt, dzbar, dzbar, dzbar, hfd, wirtingerAntihol_sub]

end LocalSub

section Sequence

variable {n : ℕ}

/-- The closed polyannuli of the exhaustion. -/
def puncturedClosed (n : ℕ) (m : ℕ) : Set (Fin n → ℂ) :=
  closedPolyannulus (fun _ : Fin n => 1 / ((m : ℝ) + 1)) (fun _ : Fin n => (m : ℝ) + 1)

theorem puncturedClosed_subset (n m : ℕ) :
    puncturedClosed n m ⊆ puncturedExhaustion n m := by
  intro z hz i
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  refine ⟨lt_of_lt_of_le ?_ (hz i).1, lt_of_le_of_lt (hz i).2 (by linarith)⟩
  rw [div_lt_div_iff₀ h2 h1]
  linarith

/-- **The corrected sequence of local solutions on the punctured space.** -/
theorem exists_dbar_punctured_sequence {f : Fin n → (Fin n → ℂ) → ℂ}
    (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ (j j' : Fin n), ∀ z ∈ puncturedSpace n,
      dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ v : ℕ → (Fin n → ℂ) → ℂ,
      (∀ (m : ℕ), ∀ z ∈ puncturedSpace n, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v m) z) ∧
      (∀ (m : ℕ) (j : Fin n), ∀ z ∈ puncturedExhaustion n m, dzbarAt (v m) j z = f j z) ∧
      (∀ m : ℕ, DifferentiableOn ℂ (fun z => v (m + 1) z - v m z) (puncturedExhaustion n m)) ∧
      (∀ m : ℕ, ∀ z ∈ puncturedClosed n m, ‖v (m + 1) z - v m z‖ ≤ (1 / 2 : ℝ) ^ m) := by
  classical
  have hsub : ∀ m : ℕ,
      productDomain (fun _ : Fin n => annulus (1 / ((m : ℝ) + 3)) ((m : ℝ) + 3)) ⊆
        puncturedSpace n := by
    intro m z hz i
    intro hcon
    have h := (hz i).1
    rw [hcon, norm_zero] at h
    have : (0 : ℝ) < 1 / ((m : ℝ) + 3) := by positivity
    linarith
  have hstep : ∀ m : ℕ, ∃ w : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w ∧
      ∀ j : Fin n, ∀ z ∈ puncturedExhaustion n m, dzbarAt w j z = f j z := by
    intro m
    have h1 : ∀ _i : Fin n, (0 : ℝ) ≤ 1 / ((m : ℝ) + 3) := fun _ => by positivity
    have h2 : ∀ _i : Fin n, 1 / ((m : ℝ) + 3) < 1 / ((m : ℝ) + 2) := fun _ => by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h3 : ∀ _i : Fin n, 1 / ((m : ℝ) + 2) < (m : ℝ) + 2 := fun _ => by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have h4 : ∀ _i : Fin n, (m : ℝ) + 2 < (m : ℝ) + 3 := fun _ => by linarith
    exact dbar_polyannulus_solve h1 h2 h3 h4 hCf
      (fun j j' z hz => hclosed j j' z (hsub m hz))
  choose u hCu hu using hstep
  have hdu : ∀ m : ℕ, Differentiable ℝ (fun z => u (m + 1) z - u m z) := fun m =>
    ((hCu (m + 1)).differentiable (by simp)).sub ((hCu m).differentiable (by simp))
  have hdiffdu : ∀ m : ℕ, DifferentiableOn ℂ (fun z => u (m + 1) z - u m z)
      (puncturedExhaustion n m) := by
    intro m
    refine differentiableOn_complex_of_dzbarAt_eq_zero (hdu m) ?_
    intro j z hz
    rw [dzbarAt_sub ((hCu (m + 1)).differentiable (by simp))
      ((hCu m).differentiable (by simp)) j z]
    rw [hu (m + 1) j z (puncturedExhaustion_mono n m hz), hu m j z hz, sub_self]
  have happrox : ∀ m : ℕ, ∃ P : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ P (puncturedSpace n) ∧
      ∀ z ∈ puncturedClosed n m, ‖(u (m + 1) z - u m z) - P z‖ ≤ (1 / 2 : ℝ) ^ m := by
    intro m
    have h1 : ∀ _i : Fin n, (0 : ℝ) < 1 / ((m : ℝ) + 2) := fun _ => by positivity
    have h2 : ∀ _i : Fin n, 1 / ((m : ℝ) + 2) < 1 / ((m : ℝ) + 1) := fun _ => by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h3 : ∀ _i : Fin n, 1 / ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := fun _ => by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have h4 : ∀ _i : Fin n, (m : ℝ) + 1 < (m : ℝ) + 2 := fun _ => by linarith
    obtain ⟨P, hPholo, hPapp⟩ := exists_punctured_approx_polyannulus n
      (fun z => u (m + 1) z - u m z)
      (fun _ => 1 / ((m : ℝ) + 2)) (fun _ => (m : ℝ) + 2)
      (fun _ => 1 / ((m : ℝ) + 1)) (fun _ => (m : ℝ) + 1) ((1 / 2 : ℝ) ^ m)
      h1 h2 h3 h4 (by positivity) (hdiffdu m)
    exact ⟨P, hPholo, hPapp⟩
  choose P hPholo hPapprox using happrox
  have hPsmooth : ∀ (l : ℕ), ∀ z ∈ puncturedSpace n,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P l) z := fun l z hz =>
    contDiffAt_of_differentiableOn isOpen_puncturedSpace (hPholo l) hz
  have hSsmooth : ∀ (m : ℕ), ∀ z ∈ puncturedSpace n,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w) z := by
    intro m z hz
    induction m with
    | zero => simpa using contDiffAt_const
    | succ m ih =>
        have heq : (fun w : Fin n → ℂ => ∑ l ∈ Finset.range (m + 1), P l w)
            = fun w : Fin n → ℂ => (∑ l ∈ Finset.range m, P l w) + P m w := by
          funext w
          rw [Finset.sum_range_succ]
        rw [heq]
        exact ih.add (hPsmooth m z hz)
  have hSholo : ∀ m : ℕ, DifferentiableOn ℂ
      (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w) (puncturedSpace n) := by
    intro m
    have heq : (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w)
        = ∑ l ∈ Finset.range m, P l := by
      funext w
      simp [Finset.sum_apply]
    rw [heq]
    exact DifferentiableOn.sum fun l _ => hPholo l
  have hdiffstep : ∀ m : ℕ, (fun z : Fin n → ℂ =>
      (u (m + 1) z - ∑ l ∈ Finset.range (m + 1), P l z) -
        (u m z - ∑ l ∈ Finset.range m, P l z))
      = fun z : Fin n → ℂ => (u (m + 1) z - u m z) - P m z := by
    intro m
    funext z
    rw [Finset.sum_range_succ]
    ring
  refine ⟨fun m z => u m z - ∑ l ∈ Finset.range m, P l z, ?_, ?_, ?_, ?_⟩
  · intro m z hz
    exact ((hCu m).contDiffAt).sub (hSsmooth m z hz)
  · intro m j z hz
    show dzbarAt (fun w => u m w - ∑ l ∈ Finset.range m, P l w) j z = f j z
    have hzZ : z ∈ puncturedSpace n := by
      intro i
      intro hcon
      have h := (hz i).1
      rw [hcon, norm_zero] at h
      have : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
      linarith
    have hSdiff : DifferentiableAt ℝ (fun w : Fin n → ℂ => ∑ l ∈ Finset.range m, P l w) z :=
      (hSsmooth m z hzZ).differentiableAt (by simp)
    rw [dzbarAt_sub_at ((hCu m).differentiable (by simp) z) hSdiff j,
      dzbarAt_eq_zero_of_differentiableOn isOpen_puncturedSpace (hSholo m) hzZ j,
      hu m j z hz, sub_zero]
  · intro m
    have hEsub : puncturedExhaustion n m ⊆ puncturedSpace n := by
      intro z hz i hcon
      have h := (hz i).1
      rw [hcon, norm_zero] at h
      have : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
      linarith
    rw [hdiffstep m]
    exact (hdiffdu m).sub ((hPholo m).mono hEsub)
  · intro m z hz
    have h := congrFun (hdiffstep m) z
    rw [h]
    exact hPapprox m z hz

end Sequence

section Limit

variable {n : ℕ}

/-- The closed exhaustion increases. -/
theorem puncturedClosed_mono (n m : ℕ) : puncturedClosed n m ⊆ puncturedClosed n (m + 1) := by
  intro z hz i
  refine ⟨le_trans ?_ (hz i).1, le_trans (hz i).2 ?_⟩
  · push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · push_cast
    linarith

/-- **Every point of the punctured space lies in all late closed polyannuli.** -/
theorem exists_mem_puncturedClosed {z : Fin n → ℂ} (hz : z ∈ puncturedSpace n) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → z ∈ puncturedClosed n m := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨0, fun m _ i => absurd i.isLt (by omega)⟩
  · have hpos : ∀ i, 0 < ‖z i‖ := fun i => norm_pos_iff.2 (hz i)
    obtain ⟨m₁, hm₁⟩ := exists_nat_gt (‖z‖)
    obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℕ, ∀ i, (‖z i‖)⁻¹ < (m₂ : ℝ) := by
      obtain ⟨B, hB⟩ := (Set.finite_range fun i => (‖z i‖)⁻¹).bddAbove
      obtain ⟨m₂, hm₂⟩ := exists_nat_gt B
      exact ⟨m₂, fun i => lt_of_le_of_lt (hB (Set.mem_range_self i)) hm₂⟩
    refine ⟨max m₁ m₂, fun m hm i => ?_⟩
    have hmc : ((max m₁ m₂ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1c : ((m₁ : ℕ) : ℝ) ≤ (m : ℝ) :=
      le_trans (by exact_mod_cast le_max_left m₁ m₂) hmc
    have h2c : ((m₂ : ℕ) : ℝ) ≤ (m : ℝ) :=
      le_trans (by exact_mod_cast le_max_right m₁ m₂) hmc
    have hzi : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      have h1 : (‖z i‖)⁻¹ < (m₂ : ℝ) := hm₂ i
      have h3 : (‖z i‖)⁻¹ < (m : ℝ) + 1 := by linarith
      rw [inv_lt_iff_one_lt_mul₀ (hpos i)] at h3
      linarith
    · have h1 : ‖z i‖ < (m₁ : ℝ) := lt_of_le_of_lt hzi hm₁
      linarith

end Limit

section Solve

variable {n : ℕ}

/-- The open exhaustion sits inside the next closed one. -/
theorem puncturedExhaustion_subset_closed (n m : ℕ) :
    puncturedExhaustion n m ⊆ puncturedClosed n (m + 1) := by
  intro z hz i
  have h1 := (hz i).1
  have h2 := (hz i).2
  have hcast : (((m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) + 2 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · simp only [hcast]
    linarith
  · simp only [hcast]
    linarith

/-- **Global solvability of the `∂̄` system on `(ℂ^×)^n`.**  The corrected local solutions converge
locally uniformly, their differences are holomorphic by Weierstrass' theorem, and the limit solves
the system on the whole punctured space. -/
theorem dbar_punctured_solve {f : Fin n → (Fin n → ℂ) → ℂ}
    (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ (j j' : Fin n), ∀ z ∈ puncturedSpace n,
      dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ u : (Fin n → ℂ) → ℂ,
      (∀ z ∈ puncturedSpace n, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u z) ∧
      ∀ (j : Fin n), ∀ z ∈ puncturedSpace n, dzbarAt u j z = f j z := by
  classical
  obtain ⟨v, hCv, hsolve, hholo, hest⟩ := exists_dbar_punctured_sequence hCf hclosed
  set D : ℕ → (Fin n → ℂ) → ℂ := fun m z => v (m + 1) z - v m z with hD
  have hclosedmono : ∀ (m m' : ℕ), m ≤ m' → puncturedClosed n m ⊆ puncturedClosed n m' := by
    intro m m' hmm'
    induction m' with
    | zero =>
        have : m = 0 := Nat.le_zero.1 hmm'
        rw [this]
    | succ k ihk =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hmm') with h | h
        · exact (ihk (Nat.lt_succ_iff.1 h)).trans (puncturedClosed_mono n k)
        · rw [h]
  have hDsummable : ∀ z ∈ puncturedSpace n, Summable fun m => D m z := by
    intro z hz
    obtain ⟨M, hM⟩ := exists_mem_puncturedClosed hz
    refine Summable.of_norm_bounded_eventually summable_geometric_two ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    exact hest m z (hM m hm)
  set w : (Fin n → ℂ) → ℂ := fun z => v 0 z + ∑' m, D m z with hw
  have htele : ∀ z ∈ puncturedSpace n, ∀ N : ℕ, w z - v N z = ∑' m, D (m + N) z := by
    intro z hz N
    have h1 : ∑ i ∈ Finset.range N, D i z = v N z - v 0 z :=
      Finset.sum_range_sub (fun k => v k z) N
    have h2 := (hDsummable z hz).sum_add_tsum_nat_add N
    show v 0 z + ∑' m, D m z - v N z = _
    rw [← h2, h1]
    ring
  have htail : ∀ (N : ℕ) (z : Fin n → ℂ), z ∈ puncturedClosed n N → z ∈ puncturedSpace n →
      ‖w z - v N z‖ ≤ 2 * (1 / 2 : ℝ) ^ N := by
    intro N z hzN hz
    have hb : ∀ m : ℕ, ‖D (m + N) z‖ ≤ (1 / 2 : ℝ) ^ (m + N) :=
      fun m => hest (m + N) z (hclosedmono N (m + N) (Nat.le_add_left N m) hzN)
    have hsg : Summable fun m : ℕ => (1 / 2 : ℝ) ^ (m + N) := by
      simpa [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ N)
    have hns : Summable fun m : ℕ => ‖D (m + N) z‖ :=
      hsg.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    rw [htele z hz N]
    refine le_trans (norm_tsum_le_tsum_norm hns) ?_
    refine le_trans (Summable.tsum_le_tsum hb hns hsg) ?_
    have heq : ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + N) = 2 * (1 / 2 : ℝ) ^ N := by
      simp only [pow_add]
      rw [tsum_mul_right, tsum_geometric_two]
    exact le_of_eq heq
  -- uniform convergence on the closed polyannuli
  have hunif : ∀ M : ℕ, TendstoUniformlyOn (fun (N : ℕ) (z : Fin n → ℂ) => v N z) w
      Filter.atTop (puncturedClosed n M) := by
    intro M
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hzero : Filter.Tendsto (fun N : ℕ => 2 * (1 / 2 : ℝ) ^ N) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      simpa using this.const_mul 2
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hzero) ε hε
    filter_upwards [Filter.eventually_ge_atTop (max N₀ M)] with N hN z hz
    have hzN : z ∈ puncturedClosed n N :=
      hclosedmono M N (le_trans (le_max_right N₀ M) hN) hz
    have hzZ : z ∈ puncturedSpace n := by
      intro i hcon
      have h := (hzN i).1
      rw [hcon, norm_zero] at h
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith
    have h1 := htail N z hzN hzZ
    have h2 := hN₀ N (le_trans (le_max_left N₀ M) hN)
    rw [Real.dist_eq, sub_zero] at h2
    rw [dist_eq_norm]
    calc ‖w z - v N z‖ ≤ 2 * (1 / 2 : ℝ) ^ N := h1
      _ ≤ |2 * (1 / 2 : ℝ) ^ N| := le_abs_self _
      _ < ε := h2
  -- the limit is continuous and its difference from a member is holomorphic
  have hwcontOn : ∀ M : ℕ, ContinuousOn w (puncturedClosed n M) := by
    intro M
    refine (hunif M).continuousOn (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun N => ?_))
    refine ContinuousOn.mono ?_ (puncturedClosed_subset n M)
    exact fun z hz => ((hCv N z (by
      intro i hcon
      have h := (hz i).1
      rw [hcon, norm_zero] at h
      have : (0 : ℝ) < 1 / ((M : ℝ) + 2) := by positivity
      linarith)).continuousAt).continuousWithinAt
  have hexmono : ∀ (m m' : ℕ), m ≤ m' →
      puncturedExhaustion n m ⊆ puncturedExhaustion n m' := by
    intro m m' hmm'
    induction m' with
    | zero =>
        have : m = 0 := Nat.le_zero.1 hmm'
        rw [this]
    | succ k ihk =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hmm') with h | h
        · exact (ihk (Nat.lt_succ_iff.1 h)).trans (puncturedExhaustion_mono n k)
        · rw [h]
  have hZsub : ∀ m : ℕ, puncturedExhaustion n m ⊆ puncturedSpace n := by
    intro m z hz i hcon
    have h := (hz i).1
    rw [hcon, norm_zero] at h
    have : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  have hballdiff : ∀ (N : ℕ) (z₀ : Fin n → ℂ) (δ : ℝ), 0 < δ →
      Metric.ball z₀ δ ⊆ puncturedExhaustion n N →
      DifferentiableOn ℂ (fun z => w z - v N z) (Metric.ball z₀ δ) := by
    intro N z₀ δ hδ hsub
    have hballZ : Metric.ball z₀ δ ⊆ puncturedSpace n := hsub.trans (hZsub N)
    have hballC : Metric.ball z₀ δ ⊆ puncturedClosed n (N + 1) :=
      hsub.trans (puncturedExhaustion_subset_closed n N)
    have hGholo : ∀ k : ℕ, DifferentiableOn ℂ (fun z => v (k + N) z - v N z)
        (Metric.ball z₀ δ) := by
      intro k
      induction k with
      | zero => simpa using differentiableOn_const (0 : ℂ)
      | succ k ihk =>
          have heq : (fun z => v (k + 1 + N) z - v N z)
              = fun z => (v (k + N + 1) z - v (k + N) z) + (v (k + N) z - v N z) := by
            funext z
            rw [show k + 1 + N = k + N + 1 by ring]
            ring
          rw [heq]
          refine DifferentiableOn.add ?_ ihk
          exact (hholo (k + N)).mono
            (hsub.trans (hexmono N (k + N) (Nat.le_add_left N k)))
    have hFcont : ∀ k : ℕ, ContinuousOn (fun z => v (k + N) z - v N z) (Metric.ball z₀ δ) :=
      fun k z hz => (((hCv (k + N) z (hballZ hz)).continuousAt.sub
        (hCv N z (hballZ hz)).continuousAt)).continuousWithinAt
    have hgcont : ContinuousOn (fun z => w z - v N z) (Metric.ball z₀ δ) := by
      refine ContinuousOn.sub ((hwcontOn (N + 1)).mono hballC) ?_
      exact fun z hz => ((hCv N z (hballZ hz)).continuousAt).continuousWithinAt
    refine differentiableOn_of_tendstoUniformlyOn hδ hFcont hGholo hgcont ?_
    intro ρ hρ0 hρδ
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 (hunif (N + 1)) ε hε)
    filter_upwards [Filter.eventually_ge_atTop N₁] with k hk z hz
    have hzball : z ∈ Metric.ball z₀ δ :=
      Metric.closedBall_subset_ball hρδ hz
    have hzC : z ∈ puncturedClosed n (N + 1) := hballC hzball
    have hkey := hN₁ (k + N) (le_trans hk (Nat.le_add_right k N)) z hzC
    rw [dist_eq_norm] at hkey ⊢
    have heq : w z - v N z - (v (k + N) z - v N z) = w z - v (k + N) z := by ring
    rw [heq]
    exact hkey
  -- smoothness of the limit
  have hwsmooth : ∀ z ∈ puncturedSpace n, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w z := by
    intro z hz
    obtain ⟨N, hN⟩ := mem_puncturedExhaustion_of_mem hz
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1
      (isOpen_productDomain fun _ => isOpen_annulus _ _) z hN
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => w y - v N y) z :=
      contDiffAt_of_differentiableOn Metric.isOpen_ball (hballdiff N z δ hδ hsub)
        (Metric.mem_ball_self hδ)
    have h2 := h1.add (hCv N z hz)
    have heq : (fun y => (w y - v N y) + v N y) = w := by
      funext y
      ring
    rwa [heq] at h2
  refine ⟨w, hwsmooth, ?_⟩
  intro j z hz
  obtain ⟨N, hN⟩ := mem_puncturedExhaustion_of_mem hz
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1
    (isOpen_productDomain fun _ => isOpen_annulus _ _) z hN
  have hdw : DifferentiableAt ℝ w z := (hwsmooth z hz).differentiableAt (by simp)
  have hdvN : DifferentiableAt ℝ (v N) z := (hCv N z hz).differentiableAt (by simp)
  have hsub' := dzbarAt_sub_at hdw hdvN j
  have hzero : dzbarAt (fun x => w x - v N x) j z = 0 :=
    dzbarAt_eq_zero_of_differentiableOn Metric.isOpen_ball (hballdiff N z δ hδ hsub)
      (Metric.mem_ball_self hδ) j
  rw [hzero] at hsub'
  have hfinal : dzbarAt w j z = dzbarAt (v N) j z := by
    have h := hsub'.symm
    rwa [sub_eq_zero] at h
  rw [hfinal]
  exact hsolve N j z hN

end Solve

end HTGeometry
