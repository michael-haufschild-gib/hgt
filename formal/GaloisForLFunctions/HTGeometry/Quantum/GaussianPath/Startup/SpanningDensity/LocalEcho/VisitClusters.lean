import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.LagFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Physical low-cost visits cluster on the inverse-volume time scale -/
open Filter MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section

private theorem cluster_relation (E : Set ℝ) (d b : ℝ) (hd : 0<d) (hb : 2*d≤b)
    (gap : ∀ v∈E, ∀ w∈E, |w-v|<d ∨ b < |w-v|) :
    Equivalence (fun v w : E => |w.val-v.val|<d) := by
  refine ⟨fun _ => by simpa only [sub_self,abs_zero] using hd,fun h => by rwa [abs_sub_comm],?_⟩
  intro u v w huv hvw
  rcases gap u u.property w w.property with h|h
  · exact h
  · have htri : |w.val-u.val| ≤ |w.val-v.val|+|v.val-u.val| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (w.val-v.val) (v.val-u.val)
    exact False.elim ((htri.trans_lt (by linarith only [huv,hvw,hb])).not_gt h)

/-- Below every fixed fraction less than half a gate per bond, a gap of
constant length separates visit classes of diameter O(1/N), uniformly in time. -/
theorem gaussian_visit_clusters (κ : ℝ) (hκ : κ<1/2) : ∃ A b : ℝ, 0<A ∧ 0<b ∧
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, (s:ℝ)≤κ*(n+1:ℕ) →
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let E := {t : ℝ | HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H t)}
      (∀ v∈E, ∀ w∈E, |w-v|<A/(n+1:ℕ) ∨ b < |w-v|) ∧
      Equivalence (fun v w : E => |w.val-v.val|<A/(n+1:ℕ)) := by
  let η := (1-2*κ)/2
  have hη : 0<η := by dsimp only [η]; linarith only [hκ]
  obtain ⟨A,b,hA,hb,hw⟩ := gaussian_lag_floor η hη
  obtain ⟨k,hk⟩ := exists_nat_gt (2*A/b)
  refine ⟨A,b,hA,hb,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω,eventually_ge_atTop k] with n hn hnk
  intro s hs H E
  have hp : 0<((n+1:ℕ):ℝ) := by positivity
  have hsmall : 2*(A/(n+1:ℕ))≤b := by
    have hl : (k:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show k≤n+1 by omega)
    have hh := (div_lt_iff₀ hb).mp (hk.trans_le hl)
    rw [←mul_div_assoc,div_le_iff₀ hp]; linarith only [hh]
  have hgap (v) (hv : v∈E) (w) (hw : w∈E) : |w-v|<A/(n+1:ℕ) ∨ b < |w-v| := by
    by_contra! h
    have hh := hn v (w-v) ((div_le_iff₀ hp).mp h.1) h.2 s s (1/10) (1/10) (by norm_num) hv
      (by rw [show v+(w-v)=w by ring]; exact hw)
    rw [Nat.cast_add s s] at hh
    have hbudget := mul_lt_mul_of_pos_right (show 2*κ<1-η by dsimp only [η]; linarith only [hκ]) hp
    linarith only [hh,hbudget,hs]
  exact ⟨hgap,cluster_relation E _ b (div_pos hA hp) hsmall hgap⟩

/-- At the first physical s-gate visit after any positive origin, both
signed offsets in the same window cost more than (1-η)(N−1) minus s. -/
theorem gaussian_first_physical_rebound (η : ℝ) (hη : 0<η) : ∃ A b : ℝ, 0<A ∧ 0<b ∧
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∀ s : ℕ, let v := PrecisionReturns.firstVisit H a s (1/10)
      ∀ t : ℝ, A ≤ |t| *(n+1:ℕ) → |t|≤b → ∀ j : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/10) j (unitaryEvolution H.val (v+t)) →
          (1-η)*(n+1:ℕ)-(s:ℝ)<(j:ℝ) := by
  obtain ⟨A,b,hA,hb,hw⟩ := gaussian_lag_floor η hη
  refine ⟨A,b,hA,hb,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro H a s v t hlate hshort j hfit
  have hh := hn v t hlate hshort s j (1/10) (1/10) (by norm_num)
    (PrecisionReturns.firstVisit_isLeast H a s (by norm_num : (0:ℝ)<1/10)).1.2 hfit
  rw [Nat.cast_add s j] at hh
  linarith only [hh]

#print axioms gaussian_visit_clusters
#print axioms gaussian_first_physical_rebound
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
