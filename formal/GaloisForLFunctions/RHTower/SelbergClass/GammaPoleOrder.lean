import GaloisForLFunctions.RHTower.SelbergClass.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Exact meromorphic orders of the complex Gamma function

The complex Gamma function has a simple pole at every nonpositive integer and no other poles.
Mathlib totalizes `Gamma (-n)` to zero, so the correct formal statement uses meromorphic order.
The final affine theorem gives the pole of every individual Selberg gamma factor.
-/

open Complex Filter

/-- `Gamma` has meromorphic order `-1` at zero. -/
theorem Complex.meromorphicOrderAt_Gamma_zero :
    meromorphicOrderAt Gamma 0 = (-1 : ℤ) := by
  have hid : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
  have hgamma : MeromorphicAt Gamma 0 := Meromorphic.Gamma 0
  have hprod : MeromorphicAt (id * Gamma) 0 := hid.mul hgamma
  have htendsto : Tendsto (id * Gamma) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    change Tendsto (fun z : ℂ ↦ z * Gamma z) (nhdsWithin 0 {0}ᶜ) (nhds 1)
    exact tendsto_self_mul_Gamma_nhds_zero
  have hprod_order : meromorphicOrderAt (id * Gamma) 0 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod).mp
      ⟨1, one_ne_zero, htendsto⟩
  have hadd : meromorphicOrderAt (id * Gamma) 0 =
      meromorphicOrderAt (id : ℂ → ℂ) 0 + meromorphicOrderAt Gamma 0 :=
    meromorphicOrderAt_mul hid hgamma
  rw [hprod_order, meromorphicOrderAt_id] at hadd
  have hnotop : meromorphicOrderAt Gamma 0 ≠ ⊤ := by
    intro htop
    simp [htop] at hadd
  lift meromorphicOrderAt Gamma 0 to ℤ using hnotop with n hn
  have haddZ : (0 : ℤ) = 1 + n := by exact_mod_cast hadd
  have hnZ : n = -1 := by omega
  exact_mod_cast hnZ

/-- Every nonpositive integer is a simple pole of `Gamma`. -/
theorem Complex.meromorphicOrderAt_Gamma_neg_nat (n : ℕ) :
    meromorphicOrderAt Gamma (-(n : ℂ)) = (-1 : ℤ) := by
  induction n with
  | zero =>
      simpa using meromorphicOrderAt_Gamma_zero
  | succ n ih =>
      let x : ℂ := -((n + 1 : ℕ) : ℂ)
      have hx0 : x ≠ 0 := by
        change -((n + 1 : ℕ) : ℂ) ≠ 0
        exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      have hxadd : x + 1 = -(n : ℂ) := by
        simp [x]
      have hcomp :
          meromorphicOrderAt (Gamma ∘ fun s : ℂ ↦ s + 1) x =
            meromorphicOrderAt Gamma (x + 1) := by
        apply meromorphicOrderAt_comp_of_deriv_ne_zero
        · fun_prop
        · simp
      have hrec : (Gamma ∘ fun s : ℂ ↦ s + 1) =ᶠ[nhdsWithin x {x}ᶜ]
          fun s ↦ s * Gamma s := by
        have hne : ∀ᶠ s in nhds x, s ≠ 0 := isOpen_ne.mem_nhds hx0
        filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with s hs
        exact Gamma_add_one s hs
      have hmul : meromorphicOrderAt (fun s : ℂ ↦ s * Gamma s) x =
          meromorphicOrderAt Gamma x := by
        change meromorphicOrderAt ((fun s : ℂ ↦ s) * Gamma) x =
          meromorphicOrderAt Gamma x
        exact meromorphicOrderAt_smul_of_ne_zero (f := Gamma) (g := fun s : ℂ ↦ s)
          analyticAt_id hx0
      change meromorphicOrderAt Gamma x = (-1 : ℤ)
      calc
        meromorphicOrderAt Gamma x =
            meromorphicOrderAt (fun s : ℂ ↦ s * Gamma s) x := hmul.symm
        _ = meromorphicOrderAt (Gamma ∘ fun s : ℂ ↦ s + 1) x :=
          (meromorphicOrderAt_congr hrec).symm
        _ = meromorphicOrderAt Gamma (x + 1) := hcomp
        _ = meromorphicOrderAt Gamma (-(n : ℂ)) := by rw [hxadd]
        _ = (-1 : ℤ) := ih

/-- Affine changes of variable preserve the simple order of a Gamma pole. -/
theorem Complex.meromorphicOrderAt_Gamma_affine_neg_nat
    (lambda : ℝ) (hlambda : lambda ≠ 0) (μ : ℂ) (n : ℕ) :
    meromorphicOrderAt (fun s : ℂ ↦ Gamma ((lambda : ℂ) * s + μ))
      (-((μ + n) / (lambda : ℂ))) = (-1 : ℤ) := by
  let s₀ : ℂ := -((μ + n) / (lambda : ℂ))
  have hlambdaC : (lambda : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlambda
  have harg : (lambda : ℂ) * s₀ + μ = -(n : ℂ) := by
    dsimp [s₀]
    field_simp
    ring
  have hcomp :
      meromorphicOrderAt (Gamma ∘ fun s : ℂ ↦ (lambda : ℂ) * s + μ) s₀ =
        meromorphicOrderAt Gamma ((lambda : ℂ) * s₀ + μ) := by
    apply meromorphicOrderAt_comp_of_deriv_ne_zero
    · fun_prop
    · simpa using hlambdaC
  change meromorphicOrderAt (fun s : ℂ ↦ Gamma ((lambda : ℂ) * s + μ)) s₀ =
    (-1 : ℤ)
  rw [← Function.comp_def, hcomp, harg, meromorphicOrderAt_Gamma_neg_nat]

/-- Away from nonpositive integers, `Gamma` has meromorphic order zero. -/
theorem Complex.meromorphicOrderAt_Gamma_of_not_neg_nat {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    meromorphicOrderAt Gamma z = 0 := by
  have hgamma : MeromorphicAt Gamma z := Meromorphic.Gamma z
  have han : AnalyticAt ℂ Gamma z := hgamma.analyticAt (continuousAt_Gamma z hz)
  rw [han.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (.inr (Gamma_ne_zero hz))]
  simp

/-- Exact pole classification of the complex Gamma function. -/
theorem Complex.meromorphicOrderAt_Gamma_eq_neg_one_iff (z : ℂ) :
    meromorphicOrderAt Gamma z = (-1 : ℤ) ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  constructor
  · intro horder
    by_contra h
    push Not at h
    rw [meromorphicOrderAt_Gamma_of_not_neg_nat h] at horder
    norm_num at horder
  · rintro ⟨n, rfl⟩
    exact meromorphicOrderAt_Gamma_neg_nat n

/-- Exact pole criterion for an affine Gamma factor. -/
theorem Complex.meromorphicOrderAt_Gamma_affine_eq_neg_one_iff
    (lambda : ℝ) (hlambda : lambda ≠ 0) (μ z : ℂ) :
    meromorphicOrderAt (fun s : ℂ ↦ Gamma ((lambda : ℂ) * s + μ)) z = (-1 : ℤ) ↔
      ∃ n : ℕ, (lambda : ℂ) * z + μ = -(n : ℂ) := by
  have hlambdaC : (lambda : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlambda
  have hcomp :
      meromorphicOrderAt (Gamma ∘ fun s : ℂ ↦ (lambda : ℂ) * s + μ) z =
        meromorphicOrderAt Gamma ((lambda : ℂ) * z + μ) := by
    apply meromorphicOrderAt_comp_of_deriv_ne_zero
    · fun_prop
    · simpa using hlambdaC
  rw [← Function.comp_def, hcomp]
  exact meromorphicOrderAt_Gamma_eq_neg_one_iff _

namespace RHTower

noncomputable section

/-- Meromorphic order of a Selberg gamma factor is the sum of the orders of its Gamma factors;
the positive exponential factor `Q^s` contributes order zero. -/
theorem SelbergGammaData.meromorphicOrderAt_gammaFactor
    (G : SelbergGammaData) (z : ℂ) :
    meromorphicOrderAt G.gammaFactor z =
      ∑ j, meromorphicOrderAt
        (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j)) z := by
  have hQdiff : Differentiable ℂ fun s : ℂ ↦ (G.Q : ℂ) ^ s :=
    differentiable_id.const_cpow (.inl (ofReal_ne_zero.mpr G.Q_pos.ne'))
  have hQanalytic : AnalyticOnNhd ℂ (fun s : ℂ ↦ (G.Q : ℂ) ^ s) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hQdiff
  have hQan : AnalyticAt ℂ (fun s : ℂ ↦ (G.Q : ℂ) ^ s) z :=
    hQanalytic z (Set.mem_univ z)
  have hQne : (G.Q : ℂ) ^ z ≠ 0 :=
    cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr G.Q_pos.ne'))
  have hQorder : meromorphicOrderAt (fun s : ℂ ↦ (G.Q : ℂ) ^ s) z = 0 := by
    rw [hQan.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (.inr hQne)]
    simp
  have hGamma (j : Fin G.rank) :
      MeromorphicAt (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j)) z := by
    simpa only [Function.comp_def] using
      (Meromorphic.Gamma ((G.lambda j : ℂ) * z + G.mu j)).comp_analyticAt
        (x := z) (g := fun s : ℂ ↦ (G.lambda j : ℂ) * s + G.mu j) (by fun_prop)
  have hprod : MeromorphicAt
      (∏ j, (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j))) z :=
    MeromorphicAt.prod fun j _ ↦ hGamma j
  rw [SelbergGammaData.gammaFactor,
    meromorphicOrderAt_mul hQan.meromorphicAt hprod, hQorder, zero_add]
  simpa only using
    (meromorphicOrderAt_prod (s := Finset.univ) (fun j _ ↦ hGamma j))

/-- Number of individual Gamma factors having a pole at `z`, counted with collisions. -/
noncomputable def SelbergGammaData.gammaPoleMultiplicity (G : SelbergGammaData) (z : ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j ↦
    ∃ n : ℕ, (G.lambda j : ℂ) * z + G.mu j = -(n : ℂ)).card

/-- Exact pole-multiplicity law for a concrete Selberg gamma presentation. -/
theorem SelbergGammaData.meromorphicOrderAt_gammaFactor_eq_neg_multiplicity
    (G : SelbergGammaData) (z : ℂ) :
    meromorphicOrderAt G.gammaFactor z =
      -((G.gammaPoleMultiplicity z : ℤ) : WithTop ℤ) := by
  rw [G.meromorphicOrderAt_gammaFactor]
  classical
  have hterm (j : Fin G.rank) :
      meromorphicOrderAt
          (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j)) z =
        if ∃ n : ℕ, (G.lambda j : ℂ) * z + G.mu j = -(n : ℂ)
          then (-1 : WithTop ℤ) else 0 := by
    by_cases hpole : ∃ n : ℕ, (G.lambda j : ℂ) * z + G.mu j = -(n : ℂ)
    · rw [if_pos hpole]
      exact (Complex.meromorphicOrderAt_Gamma_affine_eq_neg_one_iff
        (G.lambda j) (G.lambda_pos j).ne' (G.mu j) z).mpr hpole
    · rw [if_neg hpole]
      have hnot : ∀ n : ℕ, (G.lambda j : ℂ) * z + G.mu j ≠ -(n : ℂ) := by
        push Not at hpole
        exact hpole
      have hcomp :
          meromorphicOrderAt
              (Gamma ∘ fun s : ℂ ↦ (G.lambda j : ℂ) * s + G.mu j) z =
            meromorphicOrderAt Gamma ((G.lambda j : ℂ) * z + G.mu j) := by
        apply meromorphicOrderAt_comp_of_deriv_ne_zero
        · fun_prop
        · simpa using ofReal_ne_zero.mpr (G.lambda_pos j).ne'
      rw [← Function.comp_def, hcomp, Complex.meromorphicOrderAt_Gamma_of_not_neg_nat hnot]
  rw [Finset.sum_congr rfl (fun j _ ↦ hterm j)]
  change (∑ j ∈ Finset.univ,
    if ∃ n : ℕ, (G.lambda j : ℂ) * z + G.mu j = -(n : ℂ)
      then (-1 : WithTop ℤ) else 0) = _
  rw [Finset.sum_ite]
  simp [SelbergGammaData.gammaPoleMultiplicity]

end

end RHTower
