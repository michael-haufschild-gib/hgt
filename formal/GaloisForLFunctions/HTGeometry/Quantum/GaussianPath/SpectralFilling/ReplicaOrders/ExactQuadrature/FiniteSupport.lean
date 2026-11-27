import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.HalfPeriods
import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature

/-! # Compressing a positive spectral clock to its number of real observables -/
open Set Real Finset
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

/-- All half-period subsums translated by the observation origin. -/
def dates : List ℝ → ℝ → Set ℝ
  | [], a => {a}
  | v::vs, a => dates vs a ∪ dates vs (a+π/|v|)

private theorem origin_mem (ws : List ℝ) (a : ℝ) : a∈dates ws a := by
  induction ws with
  | nil => rfl
  | cons _ _ ih => exact Or.inl ih

theorem dates_in_record (ws : List ℝ) (a : ℝ) : dates ws a⊆Icc a (a+length ws) := by
  induction ws generalizing a with
  | nil =>
    rintro t (rfl : t=a)
    exact ⟨le_rfl,by simp [length]⟩
  | cons v vs ih =>
    let p := π/|v|
    have hp : 0≤p := div_nonneg pi_pos.le (abs_nonneg _)
    have hl : length (v::vs)=p+length vs := rfl
    rintro t (ht|ht)
    · obtain ⟨hs,he⟩ := ih a ht
      exact ⟨hs,he.trans (by rw [hl]; linarith only [hp])⟩
    · obtain ⟨hs,he⟩ := ih (a+p) ht
      exact ⟨(le_add_of_nonneg_right hp).trans hs,he.trans_eq (by rw [hl,add_assoc])⟩

private def readings {n : ℕ} (ws : List ℝ) (f : ℝ → Fin n → ℝ) (a : ℝ) :=
  fun j => (average ws (fun t => (f t j:ℂ)) a).re

private theorem readings_mem {n : ℕ} (ws : List ℝ) (f : ℝ → Fin n → ℝ) (a : ℝ) :
    readings ws f a∈convexHull ℝ (f '' dates ws a) := by
  induction ws generalizing a with
  | nil =>
    exact subset_convexHull ℝ _ ⟨a,rfl,rfl⟩
  | cons w ws ih =>
    let b := a+π/|w|
    let X := convexHull ℝ (f '' dates (w::ws) a)
    have h₁ : readings ws f a∈X := convexHull_mono (image_mono (fun _ ht => Or.inl ht)) (ih a)
    have h₂ : readings ws f b∈X := convexHull_mono (image_mono (fun _ ht => Or.inr ht)) (ih b)
    have h := (convex_convexHull ℝ (f '' dates (w::ws) a)) h₁ h₂
      (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    have he : readings (w::ws) f a=(1/2:ℝ) • readings ws f a+(1/2:ℝ) • readings ws f b := by
      funext i
      change ((average ws (fun t => (f t i:ℂ)) a+average ws (fun t => (f t i:ℂ)) b)/2).re=
        1/2*(average ws (fun t => (f t i:ℂ)) a).re+1/2*(average ws (fun t => (f t i:ℂ)) b).re
      rw [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.div_ofReal_re,Complex.add_re]
      ring
    rw [he]
    exact h

/-- Any n real observables on the same half-period clock admit common
nonnegative weights on at most n+1 of its physical dates, exactly
preserving all n averages. No regularity of the observables is needed. -/
theorem compress_readings {n : ℕ} (ws : List ℝ) (a : ℝ) (f : ℝ → Fin n → ℝ) :
    ∃ p t : Fin (n+1) → ℝ, (∀ i, 0≤p i) ∧ (∑ i, p i=1) ∧
      (∀ i, t i∈dates ws a) ∧ ∀ j, ∑ i, p i*f (t i) j=(average ws (fun u => (f u j:ℂ)) a).re := by
  have hn : (f '' dates ws a).Nonempty := ⟨f a,a,origin_mem ws a,rfl⟩
  obtain ⟨p,z,hp,hz,he⟩ := convexHull_subset_atomicSpan hn (readings_mem ws f a)
  choose t ht hval using hz
  refine ⟨p,t,hp.1,hp.2,ht,fun j => ?_⟩
  have h := congrFun he j
  simpa only [←hval,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,readings] using h

#print axioms compress_readings
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
