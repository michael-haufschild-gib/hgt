import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalNonzeroModes

/-!
# Guth–Maynard §6: `S₂` as a sum over three planes

Guth–Maynard (arXiv:2405.20552, Lemma 4.5 and §5) write the nonzero frequencies of the cubic trace as
`I_m = N³ Σ_{t₁,t₂,t₃∈W} ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(m₃N)` and let `S₂` be the sum of the
`I_m` with exactly two nonzero `mᵢ`.  The proof of Proposition 6.1 starts from

`S₂ = 3N³ Σ_{m₁,m₂≠0} Σ_{t₁,t₂,t₃∈W} ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(0)`   ("by symmetry").

This module proves the exact form

`S₂ = 3N³ Σ_{x,y,z∈W} A(x−y) A(y−z) ĥ_{z−x}(0)`,   `A(τ) = Σ_{m≠0} ĥ_τ(mN)`,

for the Chen–Gupta–Li bump: the exactly-two-nonzero frequencies are the disjoint union of three
punctured planes; on each plane the frequency sum factorizes into two absolutely convergent
punctured sums (Lemma 4.3 decay), and the three plane sums agree after a cyclic relabelling of
`(x, y, z)`.  For `q = 1` this `I_m` is the Chen–Gupta–Li trace coefficient
`cglLemma45TraceFrequencyTerm` (the residue and character factors are trivial).
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform

noncomputable section

namespace RHTower.GuthMaynard

/-- `ĥ_τ(ξ)` for the Chen–Gupta–Li bump `h_τ(u) = w(u)² u^{iτ}`. -/
abbrev gmHat (w : CGLRealSmoothBump) (τ ξ : ℝ) : ℂ :=
  𝓕 (cglSmoothBumpHt w.toCGLSmoothBump τ : ℝ → ℂ) ξ

/-- `A(τ) = Σ_{m ≠ 0} ĥ_τ(mN)`. -/
abbrev gmNonzero (w : CGLRealSmoothBump) (N τ : ℝ) : ℂ :=
  cglGMNonzeroModeSum w.toCGLSmoothBump N τ

/-- Guth–Maynard's `I_m = N³ Σ_{x,y,z∈W} ĥ_{x−y}(m₁N) ĥ_{y−z}(m₂N) ĥ_{z−x}(m₃N)`. -/
def gmIm (w : CGLRealSmoothBump) (N : ℝ) (W : Finset ℝ) (m : (ℤ × ℤ) × ℤ) : ℂ :=
  (N : ℂ) ^ 3 * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W,
    gmHat w (x - y) (m.1.1 * N) * gmHat w (y - z) (m.1.2 * N) * gmHat w (z - x) (m.2 * N)

/-- Frequencies with exactly two nonzero coordinates: the carrier of `S₂`. -/
def gmS2Frequency (m : (ℤ × ℤ) × ℤ) : Prop :=
  (m.1.1 ≠ 0 ∧ m.1.2 ≠ 0 ∧ m.2 = 0) ∨ (m.1.1 = 0 ∧ m.1.2 ≠ 0 ∧ m.2 ≠ 0) ∨
    (m.1.1 ≠ 0 ∧ m.1.2 = 0 ∧ m.2 ≠ 0)

/-- Guth–Maynard's `S₂ = Σ_{m exactly two nonzero} I_m`. -/
def gmS2 (w : CGLRealSmoothBump) (N : ℝ) (W : Finset ℝ) : ℂ :=
  ∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m}, gmIm w N W m

/-- Punctured integers. -/
local notation "P" => CGLProposition51PuncturedFrequency

/-- The plane `m₃ = 0`. -/
def gmPlaneThree (p : P × P) : (ℤ × ℤ) × ℤ := ((p.1.1, p.2.1), 0)
/-- The plane `m₁ = 0`. -/
def gmPlaneOne (p : P × P) : (ℤ × ℤ) × ℤ := ((0, p.1.1), p.2.1)
/-- The plane `m₂ = 0`. -/
def gmPlaneTwo (p : P × P) : (ℤ × ℤ) × ℤ := ((p.2.1, 0), p.1.1)

theorem gmS2Frequency.fst_ne_zero {m : (ℤ × ℤ) × ℤ} (h : gmS2Frequency m) (h₃ : m.2 = 0) :
    m.1.1 ≠ 0 := by
  rcases h with h | h | h
  · exact h.1
  · exact absurd h₃ h.2.2
  · exact absurd h₃ h.2.2

theorem gmS2Frequency.snd_ne_zero {m : (ℤ × ℤ) × ℤ} (h : gmS2Frequency m) (h₃ : m.2 = 0) :
    m.1.2 ≠ 0 := by
  rcases h with h | h | h
  · exact h.2.1
  · exact absurd h₃ h.2.2
  · exact absurd h₃ h.2.2

theorem gmS2Frequency.snd_ne_zero' {m : (ℤ × ℤ) × ℤ} (h : gmS2Frequency m) (h₃ : m.2 ≠ 0)
    (h₁ : m.1.1 = 0) : m.1.2 ≠ 0 := by
  rcases h with h | h | h
  · exact absurd h.2.2 h₃
  · exact h.2.1
  · exact absurd h₁ h.1

/-- The `S₂` carrier is the disjoint union of three punctured planes. -/
def gmS2FrequencyEquiv :
    {m : (ℤ × ℤ) × ℤ // gmS2Frequency m} ≃ ((P × P) ⊕ (P × P) ⊕ (P × P)) where
  toFun x := by
    classical
    exact if h₃ : x.1.2 = 0 then
      Sum.inl (⟨x.1.1.1, x.2.fst_ne_zero h₃⟩, ⟨x.1.1.2, x.2.snd_ne_zero h₃⟩)
    else if h₁ : x.1.1.1 = 0 then
      Sum.inr (Sum.inl (⟨x.1.1.2, x.2.snd_ne_zero' h₃ h₁⟩, ⟨x.1.2, h₃⟩))
    else
      Sum.inr (Sum.inr (⟨x.1.2, h₃⟩, ⟨x.1.1.1, h₁⟩))
  invFun
    | Sum.inl p => ⟨gmPlaneThree p, Or.inl ⟨p.1.2, p.2.2, rfl⟩⟩
    | Sum.inr (Sum.inl p) => ⟨gmPlaneOne p, Or.inr (Or.inl ⟨rfl, p.1.2, p.2.2⟩)⟩
    | Sum.inr (Sum.inr p) => ⟨gmPlaneTwo p, Or.inr (Or.inr ⟨p.2.2, rfl, p.1.2⟩)⟩
  left_inv x := by
    rcases x with ⟨⟨⟨m₁, m₂⟩, m₃⟩, h⟩
    rcases h with h | h | h
    · apply Subtype.ext
      change m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ = 0 at h
      simp only [dif_pos h.2.2]
      change ((m₁, m₂), 0) = ((m₁, m₂), m₃)
      rw [h.2.2]
    · apply Subtype.ext
      change m₁ = 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 at h
      simp only [dif_neg h.2.2, dif_pos h.1]
      change ((0, m₂), m₃) = ((m₁, m₂), m₃)
      rw [h.1]
    · apply Subtype.ext
      change m₁ ≠ 0 ∧ m₂ = 0 ∧ m₃ ≠ 0 at h
      simp only [dif_neg h.2.2, dif_neg h.1]
      change ((m₁, 0), m₃) = ((m₁, m₂), m₃)
      rw [h.2.1]
  right_inv x := by
    rcases x with p | p | p
    · simp [gmPlaneThree]
    · simp [gmPlaneOne, p.1.2]
    · simp [gmPlaneTwo, p.1.2, p.2.2]

/-- Absolute summability of `m ↦ ĥ_τ(mN)` over the punctured integers. -/
theorem summable_norm_gmHat_punctured (w : CGLRealSmoothBump) {N : ℝ} (hN : 0 < N) (τ : ℝ) :
    Summable fun m : P => ‖gmHat w τ ((m : ℝ) * N)‖ :=
  (summable_norm_fourier_cglSmoothBumpHt_int w.toCGLSmoothBump τ N hN).subtype _

/-- On a plane, the frequency sum factorizes:
`Σ_{a,b≠0} ĥ_α(aN) ĥ_β(bN) c = A(α) A(β) c`. -/
theorem hasSum_gmHat_pair (w : CGLRealSmoothBump) {N : ℝ} (hN : 0 < N) (α β : ℝ) (c : ℂ) :
    HasSum (fun p : P × P => gmHat w α ((p.1 : ℝ) * N) * gmHat w β ((p.2 : ℝ) * N) * c)
      (gmNonzero w N α * gmNonzero w N β * c) := by
  have h₁ := summable_norm_gmHat_punctured w hN α
  have h₂ := summable_norm_gmHat_punctured w hN β
  have hprod : HasSum (fun p : P × P => gmHat w α ((p.1 : ℝ) * N) * gmHat w β ((p.2 : ℝ) * N))
      (gmNonzero w N α * gmNonzero w N β) := by
    have hs := summable_mul_of_summable_norm (f := fun m : P => gmHat w α ((m : ℝ) * N))
      (g := fun m : P => gmHat w β ((m : ℝ) * N)) h₁ h₂
    rw [gmNonzero, gmNonzero, cglGMNonzeroModeSum, cglGMNonzeroModeSum,
      tsum_mul_tsum_of_summable_norm h₁ h₂]
    exact hs.hasSum
  exact hprod.mul_right c

/-- `F(x,y,z) = A(x−y) A(y−z) ĥ_{z−x}(0)`. -/
def gmS2Kernel (w : CGLRealSmoothBump) (N x y z : ℝ) : ℂ :=
  gmNonzero w N (x - y) * gmNonzero w N (y - z) * gmHat w (z - x) 0

/-- The plane `m₃ = 0` sums to `N³ Σ_{x,y,z} F(x,y,z)`. -/
theorem hasSum_gmIm_planeThree (w : CGLRealSmoothBump) {N : ℝ} (hN : 0 < N) (W : Finset ℝ) :
    HasSum (fun p : P × P => gmIm w N W (gmPlaneThree p))
      ((N : ℂ) ^ 3 * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmS2Kernel w N x y z) := by
  refine HasSum.mul_left _ (hasSum_sum fun x _ => hasSum_sum fun y _ => hasSum_sum fun z _ => ?_)
  simpa [gmPlaneThree, gmS2Kernel] using hasSum_gmHat_pair w hN (x - y) (y - z) (gmHat w (z - x) 0)

/-- The plane `m₁ = 0` sums to `N³ Σ_{x,y,z} F(y,z,x)`. -/
theorem hasSum_gmIm_planeOne (w : CGLRealSmoothBump) {N : ℝ} (hN : 0 < N) (W : Finset ℝ) :
    HasSum (fun p : P × P => gmIm w N W (gmPlaneOne p))
      ((N : ℂ) ^ 3 * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmS2Kernel w N y z x) := by
  have hrw : (fun p : P × P => gmIm w N W (gmPlaneOne p)) = fun p => (N : ℂ) ^ 3 *
      ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmHat w (y - z) ((p.1 : ℝ) * N) *
        gmHat w (z - x) ((p.2 : ℝ) * N) * gmHat w (x - y) 0 := by
    funext p
    simp only [gmIm, gmPlaneOne, Int.cast_zero, zero_mul]
    congr 1
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => by ring
  rw [hrw]
  exact HasSum.mul_left _ (hasSum_sum fun x _ => hasSum_sum fun y _ => hasSum_sum fun z _ =>
    hasSum_gmHat_pair w hN _ _ _)

/-- The plane `m₂ = 0` sums to `N³ Σ_{x,y,z} F(z,x,y)`. -/
theorem hasSum_gmIm_planeTwo (w : CGLRealSmoothBump) {N : ℝ} (hN : 0 < N) (W : Finset ℝ) :
    HasSum (fun p : P × P => gmIm w N W (gmPlaneTwo p))
      ((N : ℂ) ^ 3 * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmS2Kernel w N z x y) := by
  have hrw : (fun p : P × P => gmIm w N W (gmPlaneTwo p)) = fun p => (N : ℂ) ^ 3 *
      ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmHat w (z - x) ((p.1 : ℝ) * N) *
        gmHat w (x - y) ((p.2 : ℝ) * N) * gmHat w (y - z) 0 := by
    funext p
    simp only [gmIm, gmPlaneTwo, Int.cast_zero, zero_mul]
    congr 1
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => by ring
  rw [hrw]
  exact HasSum.mul_left _ (hasSum_sum fun x _ => hasSum_sum fun y _ => hasSum_sum fun z _ =>
    hasSum_gmHat_pair w hN _ _ _)

/-- Cyclic relabelling of a triple sum over `W³`: `Σ G(y,z,x) = Σ G(x,y,z)`. -/
theorem sum_cyclic_one (W : Finset ℝ) (G : ℝ → ℝ → ℝ → ℂ) :
    ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, G y z x = ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, G x y z := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

/-- Cyclic relabelling of a triple sum over `W³`: `Σ G(z,x,y) = Σ G(x,y,z)`. -/
theorem sum_cyclic_two (W : Finset ℝ) (G : ℝ → ℝ → ℝ → ℂ) :
    ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, G z x y = ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, G x y z := by
  rw [← sum_cyclic_one W (fun x y z => G z x y)]
  exact sum_cyclic_one W G

/-- **`S₂` by symmetry (exact).** `S₂ = 3N³ Σ_{x,y,z∈W} A(x−y) A(y−z) ĥ_{z−x}(0)`. -/
theorem gmS2_eq_three_mul (w : CGLRealSmoothBump) {N : ℝ} (hN : 0 < N) (W : Finset ℝ) :
    gmS2 w N W = 3 * ((N : ℂ) ^ 3 * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmS2Kernel w N x y z) := by
  set S : ℂ := (N : ℂ) ^ 3 * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmS2Kernel w N x y z with hS
  have h3 := hasSum_gmIm_planeThree w hN W
  have h1 := hasSum_gmIm_planeOne w hN W
  have h2 := hasSum_gmIm_planeTwo w hN W
  rw [sum_cyclic_one W (gmS2Kernel w N)] at h1
  rw [sum_cyclic_two W (gmS2Kernel w N)] at h2
  -- transport the three plane sums through the equivalence
  set f : ((P × P) ⊕ (P × P) ⊕ (P × P)) → ℂ := fun s => gmIm w N W (gmS2FrequencyEquiv.symm s).1
    with hf
  have hsum : HasSum f (S + (S + S)) := by
    refine HasSum.sum (f := f) ?_ (HasSum.sum (f := fun s => f (Sum.inr s)) ?_ ?_)
    · simpa [hf, gmS2FrequencyEquiv] using h3
    · simpa [hf, gmS2FrequencyEquiv] using h1
    · simpa [hf, gmS2FrequencyEquiv] using h2
  unfold gmS2
  rw [← gmS2FrequencyEquiv.symm.tsum_eq (fun m => gmIm w N W m.1), hsum.tsum_eq]
  ring

end RHTower.GuthMaynard
