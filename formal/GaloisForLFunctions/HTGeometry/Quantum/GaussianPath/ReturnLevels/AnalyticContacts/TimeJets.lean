import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.AnalyticContacts.TransverseStrata
import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage

/-! # Countable flat heights on a plane analytic zero set -/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
noncomputable section

/-- Differentiate only in the time coordinate, retaining the height as
a parameter. -/
def timeJet (P : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => P
  | n+1 => fun z => fderiv ℝ (timeJet P n) z (1,0)

private theorem jet_analytic {P : ℝ × ℝ → ℝ} (ha : ∀ z, AnalyticAt ℝ P z) (n : ℕ) :
    ∀ z, AnalyticAt ℝ (timeJet P n) z := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    intro z
    let L := ContinuousLinearMap.apply ℝ ℝ ((1,0):ℝ × ℝ)
    exact (L.analyticAt _).comp (ih z).fderiv

private theorem slice_jet {P : ℝ × ℝ → ℝ} (ha : ∀ z, AnalyticAt ℝ P z) (e : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => P (t,e)) = fun t => timeJet P n (t,e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact ((jet_analytic ha n (t,e)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t e))).deriv

/-- A nonzero analytic certificate admits at most countably many
heights on a graph whose increments are quadratic on the contact set.
A nonhorizontal slice has finite time order at every zero. Removing
all but one of these time derivatives gives a transverse stratum. -/
theorem flat_heights_countable {S : Set ℝ} {f : ℝ → ℝ} (K : ℝ)
    (hflat : ∀ x ∈ S, ∀ y ∈ S, |f y-f x| ≤ K*|y-x|^2)
    (P : ℝ × ℝ → ℝ) (ha : ∀ z, AnalyticAt ℝ P z) (hn : ∃ z, P z≠0) :
    (f '' {x ∈ S | P (x,f x)=0}).Countable := by
  obtain ⟨⟨a,b⟩,hab⟩ := hn
  let H := {e : ℝ | P (a,e)=0}
  have hH : H.Countable := analytic_zero_set_countable
    (fun e _ => (ha (a,e)).comp (analyticAt_const.prod analyticAt_id)) ⟨b,hab⟩
  let T (n : ℕ) := {x ∈ S | timeJet P n (x,f x)=0 ∧ timeJet P (n+1) (x,f x)≠0}
  have hT (n : ℕ) : (T n).Countable := by
    apply countable_transverse K (fun x hx y hy => hflat x hx.1 y hy.1) (timeJet P n)
      (fun z => (jet_analytic ha n z).differentiableAt) (fun x hx => hx.2.1)
    exact fun x hx => hx.2.2
  apply (hH.union (countable_iUnion fun n => (hT n).image f)).mono
  rintro _ ⟨t,⟨ht,hz⟩,rfl⟩
  by_cases hh : f t ∈ H
  · exact Or.inl hh
  · right
    let ψ (u : ℝ) := P (u,f t)
    have hψ (u : ℝ) : AnalyticAt ℝ ψ u :=
      (ha (u,f t)).comp (analyticAt_id.prod analyticAt_const)
    have hn : analyticOrderAt ψ t ≠ ⊤ := by
      intro htop
      have hf := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero t hψ).mp htop
      apply hh
      exact congrFun hf a
    obtain ⟨n,ho⟩ := ENat.ne_top_iff_exists.mp hn
    obtain ⟨hzero,hpos⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hψ t)).mp ho.symm
    cases n with
    | zero => exact (hpos (by simpa [ψ] using hz)).elim
    | succ n =>
      apply mem_iUnion.mpr
      refine ⟨n,t,⟨ht,?_,?_⟩,rfl⟩
      · exact congrFun (slice_jet ha (f t) n).symm t |>.trans (hzero n (Nat.lt_succ_self _))
      · exact fun h => hpos ((congrFun (slice_jet ha (f t) (n+1)) t).trans h)

#print axioms flat_heights_countable
end
end GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
