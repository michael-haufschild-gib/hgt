import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstAscent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # Early returns constrain subsequent first crossings on the same orbit -/
open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
open SharpOccupation
noncomputable section

/-- A circuit for time v translates a whole affordable interval. Each further
translation costs the same number of gates and the same additional error. -/
private theorem translate_prefix {N P s : ℕ} (H : selfAdjoint (Register N))
    {σ v α δ : ℝ} (hpre : ∀ t : ℝ, |t| ≤ σ → t ∈ visitSet H P α)
    (hv : v ∈ visitSet H s δ) (m : ℕ) (t : ℝ) (ht : |t-(m:ℝ)*v| ≤ σ) :
    t ∈ visitSet H (P+m*s) (α+(m:ℝ)*δ) := by
  induction m generalizing t with
  | zero =>
    simpa only [Nat.cast_zero,zero_mul,add_zero,Nat.zero_mul,Nat.add_zero] using
      (hpre t (by simpa only [Nat.cast_zero,zero_mul,sub_zero] using ht))
  | succ m ih =>
    have hw : |(t-v)-(m:ℝ)*v| ≤ σ := by
      rw [show t-v-(m:ℝ)*v = t-((m+1:ℕ):ℝ)*v by push_cast; ring]
      exact ht
    have hp := LocalPatches.approx_product (unitaryEvolution_mem_unitary H.2 v) (ih (t-v) hw) hv
    rw [unitaryEvolution_sub_mul H t v] at hp
    simpa only [visitSet,mem_setOf_eq,Nat.succ_mul,Nat.add_assoc,Nat.cast_succ,add_mul,one_mul,add_assoc] using hp

/-- The intervals of radius σ about 0,v,…,mv cover the whole prefix up to
mv+σ precisely in the overlapping regime v ≤ 2σ (for v ≥ 0). -/
private theorem covered_prefix {σ v : ℝ} (hstep : v ≤ 2*σ)
    (m : ℕ) (u : ℝ) (hu : 0 ≤ u) (hend : u ≤ (m:ℝ)*v+σ) :
    ∃ i ≤ m, |u-(i:ℝ)*v| ≤ σ := by
  induction m with
  | zero =>
    exact ⟨0,le_rfl,by simpa only [Nat.cast_zero,zero_mul,sub_zero,abs_of_nonneg hu,zero_add] using hend⟩
  | succ m ih =>
    by_cases h : u ≤ (m:ℝ)*v+σ
    · obtain ⟨i,hi,hit⟩ := ih h
      exact ⟨i,hi.trans (Nat.le_succ _),hit⟩
    · refine ⟨m+1,le_rfl,abs_le.mpr ⟨?_,?_⟩⟩ <;>
        push_cast at * <;> linarith only [hend,hstep,lt_of_not_ge h]

/-- For the first 9/80 crossing σ at P gates and the first 13/10 crossing u
at twice that budget, every multiple of a cheap time stays farther than σ
from u while its cumulative gate count and error fit. In particular a first
physical-error return v by 2σ forces u past 11v+σ. -/
theorem gaussian_first_return_successive_crossings :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ u : ℝ, 0 < σ ∧ σ < u ∧
        orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        orbitCircuitDistance H (2*P) u = 13/10 ∧
        (∀ t ∈ Ico 0 u, orbitCircuitDistance H (2*P) t < 13/10) ∧
        (∀ (v δ : ℝ) (s m : ℕ), v ∈ visitSet H s δ → m*s ≤ P →
          9/80+(m:ℝ)*δ < 13/10 → σ < |u-(m:ℝ)*v|) ∧
        ∀ s : ℕ, 11*s ≤ P → ∃ v : ℝ, IsLeast ({t | σ ≤ t} ∩ visitSet H s (1/10)) v ∧
          (2*σ < v ∨ 11*v+σ < u) ∧ (u ≤ 3*σ → u+σ < v) := by
  obtain ⟨_,hc⟩ := gaussian_first_ascent_occupation
  obtain ⟨_,hf⟩ := gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [hc,hf] with ω hω hfω
  filter_upwards [hω,hfω] with k hcross hfirst
  intro N H P
  have hcap : 2*P ≤ 2^N/(32*(N+1)) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      2*P*(32*(N+1)) = P*(64*(N+1)) := by ring
      _ ≤ 2^N := Nat.div_mul_le_self _ _
  obtain ⟨u,hu,heU,hprev,_,_⟩ := hcross (2*P) hcap (13/10) ⟨by norm_num,le_rfl⟩
  obtain ⟨σ,hσ,heS,hprior,_,hvis⟩ := hfirst
  have hpos : 0 < σ := (by positivity : (0:ℝ) < 2^((k+3)-10*(k+3).sqrt)).trans hσ
  have hpre (t : ℝ) (ht : |t| ≤ σ) : t ∈ visitSet H P (9/80) := by
    have hnon (w : ℝ) (hw : 0 ≤ w) (hb : w ≤ σ) : w ∈ visitSet H P (9/80) := by
      apply (hasProjectiveCircuitApproximation_iff_infDist _ P _).mpr
      rcases lt_or_eq_of_le hb with h | rfl
      · exact (hprior w ⟨hw,h⟩).le
      · exact heS.le
    rcases le_total 0 t with h | h
    · exact hnon t h ((le_abs_self t).trans ht)
    · have hneg := HasProjectiveCircuitApproximation.neg_time H
          (hnon (-t) (neg_nonneg.mpr h) ((neg_le_abs t).trans ht))
      simpa only [visitSet,mem_setOf_eq,neg_neg] using hneg
  have hsep (v δ : ℝ) (s m : ℕ) (hv : v ∈ visitSet H s δ) (hb : m*s ≤ P)
      (he : 9/80+(m:ℝ)*δ < 13/10) : σ < |u-(m:ℝ)*v| := by
    by_contra! hnear
    obtain ⟨z,hz,C,hC,herr⟩ := translate_prefix H hpre hv m u hnear
    have hd : orbitCircuitDistance H (2*P) u ≤ 9/80+(m:ℝ)*δ :=
      (hasProjectiveCircuitApproximation_iff_infDist _ (2*P) _).mp
      ⟨z,hz,C,hC.trans (by omega),herr⟩
    exact he.not_ge (heU.ge.trans hd)
  have horder : σ < u := by
    have h := hsep 0 (9/80) P 0 (hpre 0 (by simpa only [abs_zero] using hpos.le)) (by simp) (by norm_num)
    simpa only [Nat.cast_zero,zero_mul,sub_zero,abs_of_pos hu] using h
  refine ⟨σ,u,hpos,horder,heS,hprior,heU,hprev,hsep,?_⟩
  intro s hs
  obtain ⟨v,_,hv,_,_⟩ := hvis s (by change s ≤ P/2; omega)
  have hwait : 2*σ < v ∨ 11*v+σ < u := by
    apply or_iff_not_imp_left.mpr
    intro hlate
    by_contra! h
    obtain ⟨i,hi,hit⟩ := covered_prefix (le_of_not_gt hlate) 11 u hu.le (by simpa using h)
    have herr : 9/80+(i:ℝ)*(1/10) < 13/10 := by
      have hi' : (i:ℝ) ≤ 11 := by exact_mod_cast hi
      linarith only [hi']
    exact (hsep v _ s i hv.1.2 ((Nat.mul_le_mul_right s hi).trans hs) herr).not_ge hit
  refine ⟨v,hv,hwait,fun hclose => ?_⟩
  have hvσ : σ ≤ v := hv.1.1
  have hlate : 2*σ < v := hwait.resolve_right (by linarith only [hvσ,hpos,hclose])
  have hdist := hsep v (1/10) s 1 hv.1.2 (by omega) (by norm_num)
  rw [Nat.cast_one,one_mul,lt_abs] at hdist
  rcases hdist with h | h <;> linarith only [h,hclose,hlate]


#print axioms gaussian_first_return_successive_crossings
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
