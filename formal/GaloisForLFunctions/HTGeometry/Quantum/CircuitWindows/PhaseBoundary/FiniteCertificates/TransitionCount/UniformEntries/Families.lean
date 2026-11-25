import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries.WordBounds

/-! # Uniform finite exponential expansions over a family of spectra -/

open Finset
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
noncomputable section

/-- The number of terms and the multiple of the spectral bandwidth are
chosen before the member of the family. Coefficients can vary freely. -/
def uniformExpansion {X : Type*} (W : X→ℝ) (f : X→ℝ→ℂ) : Prop :=
  ∃ m L : ℕ, ∀ x, ∃ w : Word, wordBounds m ((L:ℝ)*W x) w ∧
    ∀ t, evaluate t w=f x t

theorem uniformExpansion.const {X : Type*} (W : X→ℝ) (c : X→ℂ) :
    uniformExpansion W (fun x _ => c x) := by
  refine ⟨1,0,fun x => ⟨algebraMap ℂ Word (c x),?_,fun _ => AlgHom.commutes ..⟩⟩
  simpa only [Nat.cast_zero,zero_mul] using wordBounds.constant (c x)

theorem uniformExpansion.add {X : Type*} {W : X→ℝ} {f g : X→ℝ→ℂ}
    (hW : ∀ x, 0≤W x) (hf : uniformExpansion W f) (hg : uniformExpansion W g) :
    uniformExpansion W (fun x t => f x t+g x t) := by
  obtain ⟨m,L,hf⟩ := hf
  obtain ⟨n,J,hg⟩ := hg
  refine ⟨m+n,L+J,fun x => ?_⟩
  obtain ⟨u,hu,he⟩ := hf x
  obtain ⟨v,hv,he'⟩ := hg x
  refine ⟨u+v,(hu.add hv).mono le_rfl ?_,fun t => by rw [map_add,he,he']⟩
  rw [Nat.cast_add,add_mul]
  exact max_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hW x)))
    (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (hW x)))

theorem uniformExpansion.mul {X : Type*} {W : X→ℝ} {f g : X→ℝ→ℂ}
    (hf : uniformExpansion W f) (hg : uniformExpansion W g) :
    uniformExpansion W (fun x t => f x t*g x t) := by
  obtain ⟨m,L,hf⟩ := hf
  obtain ⟨n,J,hg⟩ := hg
  refine ⟨m*n,L+J,fun x => ?_⟩
  obtain ⟨u,hu,he⟩ := hf x
  obtain ⟨v,hv,he'⟩ := hg x
  exact ⟨u*v,by simpa only [Nat.cast_add,add_mul] using hu.mul hv,
    fun t => by rw [map_mul,he,he']⟩

/-- One term per level, before identifying equal frequencies. -/
theorem wordBounds.sum_single {I : Type*} (F : Finset I) (y c : I→ℂ) (B : ℝ)
    (h : ∀ i∈F, |(y i).im|≤B) :
    wordBounds F.card B (∑ i∈F, AddMonoidAlgebra.single (y i) (c i)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [wordBounds]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi]
    have hsingle := (wordBounds.single (y i) (c i)).mono le_rfl (h i (mem_insert_self ..))
    have hrest := ih (fun j hj => h j (mem_insert_of_mem hj))
    simpa only [max_self,Nat.add_comm 1] using hsingle.add hrest

/-- Uniform expansions with real values have a uniform zero-count constant
on every orbit on which the test is nonzero somewhere. -/
theorem uniformExpansion.zero_bound {X : Type*} {W : X→ℝ} {f : X→ℝ→ℂ}
    (hf : uniformExpansion W f) (hW : ∀ x, 0≤W x) (hr : ∀ x t, (f x t).im=0) :
    ∃ C ≥ (0:ℝ), ∀ x, (∃ t, f x t≠0) → ∀ a b : ℝ, a<b →
      ∀ Z : Finset ℝ, (∀ t∈Z, t∈Set.Icc a b) → (∀ t∈Z, f x t=0) →
        (Z.card:ℝ) ≤ C*(1+(b-a)*W x) := by
  obtain ⟨m,L,hf⟩ := hf
  let C := (3:ℝ)^m*((m:ℝ)+2)
  have hC : 0≤C := by dsimp only [C]; positivity
  refine ⟨C*(1+L),mul_nonneg hC (by positivity),?_⟩
  intro x hn a b hab Z hZ hzero
  obtain ⟨w,hw,he⟩ := hf x
  have h := bounded_word_zeros hw (mul_nonneg (Nat.cast_nonneg L) (hW x))
    (fun t => by rw [he,hr]) (by simpa only [he] using hn) a b hab Z hZ
    (fun t ht => by rw [he,hzero t ht])
  apply h.trans
  rw [mul_assoc C]
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith only [(Nat.cast_nonneg L : (0:ℝ)≤L),mul_nonneg (sub_nonneg.mpr hab.le) (hW x)]

#print axioms uniformExpansion.zero_bound
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
