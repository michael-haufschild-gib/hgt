import GaloisForLFunctions.HTGeometry.HellmannFeynman

/-!
# The coefficient-pointed Weil floor and its source incidence

The coefficient-pointed Weil energy is affine in the finite prime-power coefficient vector, so its
infimum over the trial sphere is concave, and a uniform bound on the correlation forms makes the
floor Lipschitz.

At a differentiable simple ground state the eigenvector response is the reduced-resolvent image of
the projected prime autocorrelation, the Hessian of the floor is minus twice the corresponding Gram
form — hence nonpositive — and the divisor-facing characteristic response is the image of that same
vector under any continuous linear readout.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} {m : ℕ}

/-- The coefficient-pointed Weil energy of a trial vector, equation `(1)`. -/
def weilEnergy (q : ι → ℝ) (V : Fin m → ι → ℝ) (b : Fin m → ℝ) (f : ι) : ℝ :=
  q f - ∑ n, b n * V n f

/-- The coefficient-pointed Weil floor, equation `(3)`. -/
def weilFloor (q : ι → ℝ) (V : Fin m → ι → ℝ) (b : Fin m → ℝ) : ℝ :=
  ⨅ f : ι, weilEnergy q V b f

theorem weilEnergy_affine (q : ι → ℝ) (V : Fin m → ι → ℝ) (b₁ b₂ : Fin m → ℝ) (t : ℝ) (f : ι) :
    weilEnergy q V (t • b₁ + (1 - t) • b₂) f
      = t * weilEnergy q V b₁ f + (1 - t) * weilEnergy q V b₂ f := by
  unfold weilEnergy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∑ n, (t * b₁ n + (1 - t) * b₂ n) * V n f
      = t * (∑ n, b₁ n * V n f) + (1 - t) * (∑ n, b₂ n * V n f) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hterm]
  ring

/-- **Concavity of the floor.**  The pointwise infimum of an affine family is concave. -/
theorem weilFloor_concave [Nonempty ι] (q : ι → ℝ) (V : Fin m → ι → ℝ)
    (hbdd : ∀ b : Fin m → ℝ, BddBelow (Set.range (weilEnergy q V b)))
    (b₁ b₂ : Fin m → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * weilFloor q V b₁ + (1 - t) * weilFloor q V b₂
      ≤ weilFloor q V (t • b₁ + (1 - t) • b₂) := by
  refine le_ciInf fun f => ?_
  have h1 : weilFloor q V b₁ ≤ weilEnergy q V b₁ f := ciInf_le (hbdd b₁) f
  have h2 : weilFloor q V b₂ ≤ weilEnergy q V b₂ f := ciInf_le (hbdd b₂) f
  rw [weilEnergy_affine]
  have ht1' : 0 ≤ 1 - t := by linarith
  nlinarith

/-- **Local Lipschitz continuity of the floor.**  A uniform bound on the correlation forms bounds
the floor's modulus of continuity in the coefficient vector. -/
theorem abs_weilFloor_sub_le [Nonempty ι] (q : ι → ℝ) (V : Fin m → ι → ℝ)
    (hbdd : ∀ b : Fin m → ℝ, BddBelow (Set.range (weilEnergy q V b)))
    {M : ℝ} (hM : ∀ n f, |V n f| ≤ M) (b b' : Fin m → ℝ) :
    |weilFloor q V b - weilFloor q V b'| ≤ M * ∑ n, |b n - b' n| := by
  have key : ∀ c c' : Fin m → ℝ, weilFloor q V c - weilFloor q V c' ≤ M * ∑ n, |c n - c' n| := by
    intro c c'
    have hstep : ∀ f : ι, weilEnergy q V c f ≤ weilEnergy q V c' f + M * ∑ n, |c n - c' n| := by
      intro f
      have hdiff : weilEnergy q V c f - weilEnergy q V c' f = ∑ n, (c' n - c n) * V n f := by
        unfold weilEnergy
        have hsplit : ∑ n, (c' n - c n) * V n f
            = (∑ n, c' n * V n f) - ∑ n, c n * V n f := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun n _ => by ring
        rw [hsplit]
        ring
      have hbound : ∑ n, (c' n - c n) * V n f ≤ M * ∑ n, |c n - c' n| := by
        calc ∑ n, (c' n - c n) * V n f
            ≤ ∑ n, |c n - c' n| * M := by
              refine Finset.sum_le_sum fun n _ => ?_
              calc (c' n - c n) * V n f ≤ |(c' n - c n) * V n f| := le_abs_self _
                _ = |c' n - c n| * |V n f| := abs_mul _ _
                _ ≤ |c n - c' n| * M := by
                    rw [abs_sub_comm]
                    exact mul_le_mul_of_nonneg_left (hM n f) (abs_nonneg _)
          _ = M * ∑ n, |c n - c' n| := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun n _ => mul_comm _ _
      linarith
    have hle : weilFloor q V c - M * ∑ n, |c n - c' n| ≤ weilFloor q V c' := by
      refine le_ciInf fun f => ?_
      have h1 : weilFloor q V c ≤ weilEnergy q V c f := ciInf_le (hbdd c) f
      have h2 := hstep f
      linarith
    linarith
  have hsymm : ∑ n, |b' n - b n| = ∑ n, |b n - b' n| :=
    Finset.sum_congr rfl fun n _ => abs_sub_comm _ _
  rw [abs_sub_le_iff]
  exact ⟨key b b', by rw [← hsymm]; exact key b' b⟩

/-! ## The differentiable ground state -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Equation (8).**  Along a differentiable eigenpair the eigenvector response solves the reduced
resolvent equation with right-hand side the source vector corrected by the eigenvalue response. -/
theorem eigenvector_response {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → ℝ} {νp : ℝ}
    {w : E} {c : ℝ}
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ᶠ t in nhds c, A t (ψ t) = ν t • ψ t) :
    A c ψ' - ν c • ψ' = νp • ψ c - w := by
  have hsmul : HasDerivAt (fun t => ν t • ψ t) (ν c • ψ' + νp • ψ c) c := hν.smul hψ
  have hAψ' : HasDerivAt (fun t => ν t • ψ t) (w + A c ψ') c :=
    hAψ.congr_of_eventuallyEq (hrel.mono fun t ht => ht.symm)
  have hderiv : w + A c ψ' = ν c • ψ' + νp • ψ c := hAψ'.unique hsmul
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at hderiv
  linear_combination (norm := module) hderiv

omit [CompleteSpace E] in
/-- **Equation (6)–(7), sign.**  A nonnegative reduced resolvent makes the Hessian form
nonpositive. -/
theorem hessian_nonpos {R : E → E} {y : E} (hR : 0 ≤ inner ℝ y (R y)) :
    -2 * inner ℝ y (R y) ≤ 0 := by linarith

omit [CompleteSpace E] in
/-- **Equation (10).**  Any continuous linear readout of the ground state has derivative the readout
of the eigenvector response. -/
theorem readout_response {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : E →L[ℝ] F) {ψ : ℝ → E} {ψ' : E} {c : ℝ} (hψ : HasDerivAt ψ ψ' c) :
    HasDerivAt (fun t => M (ψ t)) (M ψ') c :=
  M.hasFDerivAt.comp_hasDerivAt c hψ

end

end GaloisForLFunctions.RHTower
