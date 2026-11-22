import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.ObservableComparison

/-! # Factorial decay of the boundary error on successive path shells -/
open Finset NormedSpace Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {A : Type*} [CStarAlgebra A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

/-- Generator including the central site and the next k interaction shells. -/
def shellPrefix (g : ℕ → A) (k : ℕ) := ∑ i ∈ range (k+1), g i

private theorem far_reporter (g : ℕ → A) (x : A)
    (hg : ∀ i j, i+1<j → Commute (g i) (g j)) (hx : ∀ j, 1<j → Commute (g j) x)
    (i j : ℕ) (hij : i+1<j) (t : ℝ) : Commute (g j) (reporter (shellPrefix g i) x t) := by
  have hh : Commute (g j) (shellPrefix g i) := Commute.sum_right _ _ _ fun k hk =>
    (hg k j (by have := mem_range.mp hk; omega)).symm
  exact (((hh.neg_right.smul_right t).exp_right).mul_right (hx j (by omega))).mul_right
    ((hh.smul_right t).exp_right)

private theorem shell_bracket (g : ℕ → A) (x : A)
    (hg : ∀ i j, i+1<j → Commute (g i) (g j)) (hx : ∀ j, 1<j → Commute (g j) x)
    {k n : ℕ} (hk : k<n) (t : ℝ) :
    let y := reporter (shellPrefix g k) x t
    let d := shellPrefix g n-shellPrefix g k
    d*y-y*d=g (k+1)*y-y*g (k+1) := by
  intro y d
  let q := ∑ j ∈ Finset.Ico (k+2) (n+1), g j
  have he : shellPrefix g (k+1)+q=shellPrefix g n :=
    sum_range_add_sum_Ico g (by omega)
  have hd : d=g (k+1)+q := by
    dsimp only [d]
    rw [←he,show shellPrefix g (k+1)=shellPrefix g k+g (k+1) from sum_range_succ ..]
    abel
  have hc : Commute q y := Commute.sum_left _ _ _ fun j hj =>
    far_reporter g x hg hx k j (by have := (Finset.mem_Ico.mp hj).1; omega) t
  rw [hd,add_mul,mul_add,hc.eq]
  abel

private def coeff (B R : ℝ) (k : ℕ) := R*(2*B)^k/k.factorial

private theorem coeff_succ (B R : ℝ) (k : ℕ) :
    coeff B R (k+1)=(2*B*coeff B R k)/(k+1) := by
  simp only [coeff,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring

/-- Omitting everything outside radius k costs at most the (k+1)-st
exponential-series term. Only the shells through the first omitted one
need norm bounds, independently of the rest of the chain. -/
theorem path_shell_localization (g : ℕ → A) (x : A) (hs : ∀ i, g i∈skewAdjoint A)
    (hg : ∀ i j, i+1<j → Commute (g i) (g j)) (hx : ∀ j, 1<j → Commute (g j) x)
    (B : ℝ) (hB : 0≤B) (k n : ℕ) (hkn : k≤n) (hcap : ∀ i, i≤k+1 → ‖g i‖≤B)
    (t : ℝ) (ht : 0≤t) :
    ‖reporter (shellPrefix g k) x t-reporter (shellPrefix g n) x t‖ ≤
      ‖x‖*(2*B*t)^(k+1)/(k+1).factorial := by
  have hsk (j : ℕ) : shellPrefix g j∈skewAdjoint A := (skewAdjoint A).sum_mem fun i _ => hs i
  have hc (j : ℕ) : 0≤coeff B ‖x‖ j := by dsimp only [coeff]; positivity
  have step (j l : ℕ) (hjl : j<l) (hb : ‖g (j+1)‖≤B) (u : ℝ) (hu : 0≤u)
      (approx : ∀ s ∈ Set.Ico 0 u, ∃ z : A, Commute (g (j+1)) z ∧
        ‖reporter (shellPrefix g j) x s-z‖≤coeff B ‖x‖ j*s^j) :
      ‖reporter (shellPrefix g j) x u-reporter (shellPrefix g l) x u‖ ≤ coeff B ‖x‖ (j+1)*u^(j+1) := by
    have hbr (s : ℝ) (htime : s ∈ Set.Ico 0 u) :
        let a := g (j+1)
        let y := reporter (shellPrefix g j) x s
        ‖a*y-y*a‖≤(2*B*coeff B ‖x‖ j)*s^j := by
      intro a y
      obtain ⟨z,hz,hd⟩ := approx s htime
      have he : a*y-y*a=a*(y-z)-(y-z)*a := by rw [mul_sub,sub_mul,hz.eq]; abel
      rw [he]
      have hm := mul_le_mul hb hd (norm_nonneg _) hB
      calc ‖a*(y-z)-(y-z)*a‖ ≤ ‖a‖*‖y-z‖+‖y-z‖*‖a‖ :=
             (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
           _ = 2*(‖a‖*‖y-z‖) := by ring
           _ ≤ 2*(B*(coeff B ‖x‖ j*s^j)) := mul_le_mul_of_nonneg_left hm two_pos.le
           _ = _ := by ring
    apply (reporter_difference _ _ x (hsk l) j (2*B*coeff B ‖x‖ j) u hu
      (fun s hs => by rw [shell_bracket g x hg hx hjl]; exact hbr s hs)).trans_eq
    rw [coeff_succ]; ring
  have h (j : ℕ) : ∀ l, j≤l → (∀ i, i≤j+1 → ‖g i‖≤B) → ∀ u : ℝ, 0≤u →
      ‖reporter (shellPrefix g j) x u-reporter (shellPrefix g l) x u‖ ≤ coeff B ‖x‖ (j+1)*u^(j+1) := by
    induction j with
    | zero =>
      intro l hl hb u hu
      rcases hl.eq_or_lt with rfl|hlt
      · rw [sub_self,norm_zero]
        exact mul_nonneg (hc _) (pow_nonneg hu _)
      apply step 0 l hlt (hb 1 le_rfl) u hu
      intro s _
      refine ⟨0,Commute.zero_right _,?_⟩
      simp only [sub_zero,coeff,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one]
      unfold reporter
      rw [CStarRing.norm_mul_mem_unitary _ (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s (hsk 0))),
        CStarRing.norm_mem_unitary_mul _ (exp_mem_unitary_of_mem_skewAdjoint
          (skewAdjoint.smul_mem s ((skewAdjoint A).neg_mem (hsk 0))))]
    | succ j ih =>
      intro l hl hb u hu
      rcases hl.eq_or_lt with rfl|hlt
      · rw [sub_self,norm_zero]
        exact mul_nonneg (hc _) (pow_nonneg hu _)
      apply step (j+1) l hlt (hb (j+2) le_rfl) u hu
      intro s hs'
      refine ⟨reporter (shellPrefix g j) x s,far_reporter g x hg hx j (j+2) (by omega) s,?_⟩
      rw [norm_sub_rev]
      exact ih (j+1) (by omega) (fun i hi => hb i (by omega)) s hs'.1
  exact (h k n hkn hcap t ht).trans_eq (by rw [mul_pow]; dsimp only [coeff]; ring)

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
