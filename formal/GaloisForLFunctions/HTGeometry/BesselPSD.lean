import Mathlib

/-!
# Bessel's inequality for a positive semi-definite sesquilinear form

For a form that is additive and `ℂ`-homogeneous in its first slot, conjugate-symmetric, and positive
semi-definite on the diagonal, an orthonormal family satisfies Bessel's inequality
`∑ᵢ ‖B u (e i)‖² ≤ Re (B u u)`.  Definiteness is not needed, so the statement applies to forms
obtained as limits of positive forms — in particular to the logarithmic prime form
`⟨u,v⟩ = lim (loglog x)⁻¹ ∑_{p ≤ x} u(p) conj(v(p)) / p`.

In that setting the family `e_τ(p) = p^{2iτ}` is orthonormal, because
`∑_p p^{-1-2iθ} = log ζ(1+2iθ) + O(1)` is bounded for `θ ≠ 0` while the `θ = 0` sum is
`loglog x + O(1)`.  Bessel then bounds the sum of squares of the coefficient correlations at distinct
frequencies by the total energy.

Distinct from `GaloisForLFunctions.RHTower.TraceNorm.sum_inner_sq_le_of_orthonormal_with_zeros`,
which is Bessel in a genuine `InnerProductSpace ℂ H` (hence for a definite form).  The form used here
is only positive **semi**-definite and is given as a bare function, which is required for limits of
positive forms such as the logarithmic prime form.
-/

namespace HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Bessel's inequality for a positive semi-definite sesquilinear form.** -/
theorem bessel_of_orthonormal (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    (hpsd : ∀ x, 0 ≤ (B x x).re)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) (u : V)
    (horth : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, ‖B u (e i)‖ ^ 2 ≤ (B u u).re := by
  classical
  set c : ι → ℂ := fun i => B u (e i) with hc
  set w : V := ∑ i, c i • e i with hw
  -- additivity in the second slot, from conjugate symmetry
  have hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z := by
    intro x y z
    have h1 : B x (y + z) = (starRingEnd ℂ) (B (y + z) x) := hconj (y + z) x
    rw [h1, hadd₁, map_add, ← hconj, ← hconj]
  have hsum₁ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B (∑ i, f i • g i) z = ∑ i, f i * B (g i) z := by
    intro f g z
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty => simp [show B 0 z = 0 from by
        have := hsmul₁ 0 z z; simpa using this]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd₁, hsmul₁, ih]
  have hsum₂ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B z (∑ i, f i • g i) = ∑ i, (starRingEnd ℂ) (f i) * B z (g i) := by
    intro f g z
    have h1 : B z (∑ i, f i • g i) = (starRingEnd ℂ) (B (∑ i, f i • g i) z) :=
      hconj (∑ i, f i • g i) z
    rw [h1, hsum₁, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ← hconj]
  -- expand the four terms
  have hBwu : B w u = ∑ i, c i * (starRingEnd ℂ) (c i) := by
    rw [hw, hsum₁]
    exact Finset.sum_congr rfl fun i _ => by rw [hconj]
  have hBuw : B u w = ∑ i, (starRingEnd ℂ) (c i) * c i := by
    rw [hw, hsum₂]
  have hBww : B w w = ∑ i, c i * (starRingEnd ℂ) (c i) := by
    rw [hw]
    rw [hsum₁ c e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum₂ c e]
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single i]
    · rw [horth i i]; simp
    · intro j _ hj
      rw [horth i j]
      simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hvv : B (u - w) (u - w) = B u u - ∑ i, c i * (starRingEnd ℂ) (c i) := by
    have hsub : ∀ x y z : V, B (x - y) z = B x z - B y z := by
      intro x y z
      have h : B ((x - y) + y) z = B (x - y) z + B y z := hadd₁ _ _ _
      simp only [sub_add_cancel] at h
      linear_combination -h
    have hsub₂ : ∀ x y z : V, B x (y - z) = B x y - B x z := by
      intro x y z
      have h1 : B x (y - z) = (starRingEnd ℂ) (B (y - z) x) := hconj (y - z) x
      rw [h1, hsub, map_sub, ← hconj, ← hconj]
    rw [hsub, hsub₂, hsub₂, hBwu, hBuw, hBww]
    have : ∀ i, (starRingEnd ℂ) (c i) * c i = c i * (starRingEnd ℂ) (c i) := fun i => by ring
    simp only [this]
    ring
  have hnn : 0 ≤ (B (u - w) (u - w)).re := hpsd _
  rw [hvv] at hnn
  have hre : (∑ i, c i * (starRingEnd ℂ) (c i)).re = ∑ i, ‖c i‖ ^ 2 := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Complex.sub_re, hre] at hnn
  linarith


/-- **Bessel's inequality for an almost-orthogonal family.**  If the Gram entries of `e` differ
from `A` on the diagonal and from `0` off it by at most `ε` in modulus, then the coefficient
energy of any `u` is bounded by `(A + card ι · ε)` times its own energy.  Taking `ε = 0` and
`A = 1` recovers `bessel_of_orthonormal`.

The proof tests positivity on `u - λ ∑ᵢ B u (e i) • e i` and optimises the real scalar
`λ = (A + card ι · ε)⁻¹`. -/
theorem bessel_of_almost_orthogonal (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    (hpsd : ∀ x, 0 ≤ (B x x).re)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) (u : V) (A ε : ℝ)
    (hε : 0 ≤ ε) (hpos : 0 < A + Fintype.card ι * ε)
    (hgram : ∀ i j, ‖B (e i) (e j) - (if i = j then (A : ℂ) else 0)‖ ≤ ε) :
    ∑ i, ‖B u (e i)‖ ^ 2 ≤ (A + Fintype.card ι * ε) * (B u u).re := by
  classical
  set K : ℝ := A + Fintype.card ι * ε with hK
  set c : ι → ℂ := fun i => B u (e i) with hc
  set S : ℝ := ∑ i, ‖c i‖ ^ 2 with hS
  set lam : ℝ := K⁻¹ with hlam
  set w : V := ∑ i, ((lam : ℂ) * c i) • e i with hw
  -- second-slot additivity and the two summation rules
  have hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z := by
    intro x y z
    have h1 : B x (y + z) = (starRingEnd ℂ) (B (y + z) x) := hconj (y + z) x
    rw [h1, hadd₁, map_add, ← hconj, ← hconj]
  have hzero : ∀ z : V, B 0 z = 0 := by
    intro z; have := hsmul₁ 0 z z; simpa using this
  have hsum₁ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B (∑ i, f i • g i) z = ∑ i, f i * B (g i) z := by
    intro f g z
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty => simp [hzero]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd₁, hsmul₁, ih]
  have hsum₂ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B z (∑ i, f i • g i) = ∑ i, (starRingEnd ℂ) (f i) * B z (g i) := by
    intro f g z
    have h1 : B z (∑ i, f i • g i) = (starRingEnd ℂ) (B (∑ i, f i • g i) z) :=
      hconj (∑ i, f i • g i) z
    rw [h1, hsum₁, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ← hconj]
  have hsub : ∀ x y z : V, B (x - y) z = B x z - B y z := by
    intro x y z
    have h : B ((x - y) + y) z = B (x - y) z + B y z := hadd₁ _ _ _
    simp only [sub_add_cancel] at h
    linear_combination -h
  have hsub₂ : ∀ x y z : V, B x (y - z) = B x y - B x z := by
    intro x y z
    have h1 : B x (y - z) = (starRingEnd ℂ) (B (y - z) x) := hconj (y - z) x
    rw [h1, hsub, map_sub, ← hconj, ← hconj]
  -- the three mixed terms
  have hconjlam : (starRingEnd ℂ) ((lam : ℂ)) = (lam : ℂ) := Complex.conj_ofReal lam
  have hSre : (∑ i, c i * (starRingEnd ℂ) (c i)) = ((S : ℝ) : ℂ) := by
    rw [hS, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hBuw : B u w = (lam : ℂ) * ((S : ℝ) : ℂ) := by
    rw [hw, hsum₂, ← hSre, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hconjlam]
    ring
  have hBwu : B w u = (lam : ℂ) * ((S : ℝ) : ℂ) := by
    rw [hw, hsum₁, ← hSre, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hconj]
    ring
  -- the diagonal/off-diagonal split of the Gram sum
  set D : ι → ι → ℂ := fun i j => B (e i) (e j) - (if i = j then (A : ℂ) else 0) with hD
  set R : ℂ := ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * D i j with hR
  have hGram : ∀ i j, B (e i) (e j) = (if i = j then (A : ℂ) else 0) + D i j := by
    intro i j; rw [hD]; ring
  have hBww : B w w = (lam : ℂ) ^ 2 * (((A : ℂ)) * ((S : ℝ) : ℂ) + R) := by
    rw [hw, hsum₁]
    have step : ∀ i : ι, ((lam : ℂ) * c i) * B (e i) w
        = (lam : ℂ) ^ 2 * ∑ j, c i * (starRingEnd ℂ) (c j) * B (e i) (e j) := by
      intro i
      rw [hw, hsum₂, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hconjlam]
      ring
    rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.mul_sum]
    congr 1
    have hsplit : ∀ i : ι, (∑ j, c i * (starRingEnd ℂ) (c j) * B (e i) (e j))
        = c i * (starRingEnd ℂ) (c i) * (A : ℂ) + ∑ j, c i * (starRingEnd ℂ) (c j) * D i j := by
      intro i
      have hterm : ∀ j : ι, c i * (starRingEnd ℂ) (c j) * B (e i) (e j)
          = c i * (starRingEnd ℂ) (c j) * (if i = j then (A : ℂ) else 0)
            + c i * (starRingEnd ℂ) (c j) * D i j := by
        intro j; rw [hGram i j]; ring
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, ← hR]
    congr 1
    rw [← Finset.sum_mul, hSre]
    ring
  -- bound the off-diagonal remainder
  have hRbound : ‖R‖ ≤ ε * (Fintype.card ι * S) := by
    have h1 : ‖R‖ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * ε := by
      rw [hR]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hgram i j) (by positivity)
    have h2 : ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * ε = ε * (∑ i, ‖c i‖) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : (∑ i, ‖c i‖) ^ 2 ≤ Fintype.card ι * S := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖c i‖)
      simpa [hS, Finset.card_univ] using this
    calc ‖R‖ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * ε := h1
      _ = ε * (∑ i, ‖c i‖) ^ 2 := h2
      _ ≤ ε * (Fintype.card ι * S) := by exact mul_le_mul_of_nonneg_left h3 hε
  -- positivity of the tested vector
  have hnn : 0 ≤ (B (u - w) (u - w)).re := hpsd _
  have hexp : B (u - w) (u - w)
      = B u u - (lam : ℂ) * ((S : ℝ) : ℂ) - (lam : ℂ) * ((S : ℝ) : ℂ)
        + (lam : ℂ) ^ 2 * (((A : ℂ)) * ((S : ℝ) : ℂ) + R) := by
    rw [hsub, hsub₂, hsub₂, hBuw, hBwu, hBww]; ring
  rw [hexp] at hnn
  have hre : (B u u - (lam : ℂ) * ((S : ℝ) : ℂ) - (lam : ℂ) * ((S : ℝ) : ℂ)
      + (lam : ℂ) ^ 2 * (((A : ℂ)) * ((S : ℝ) : ℂ) + R)).re
      = (B u u).re - 2 * (lam * S) + lam ^ 2 * (A * S + R.re) := by
    have hre2 : ((lam : ℂ) ^ 2).re = lam ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have him2 : ((lam : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hre2, him2]
    ring
  rw [hre] at hnn
  have hReR : R.re ≤ ε * (Fintype.card ι * S) := le_trans (Complex.re_le_norm R) hRbound
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hlamK : lam * K = 1 := by rw [hlam]; field_simp
  have hquad : lam ^ 2 * (A * S + R.re) ≤ lam ^ 2 * (K * S) := by
    have : A * S + R.re ≤ K * S := by
      have : A * S + ε * (Fintype.card ι * S) = K * S := by rw [hK]; ring
      linarith [hReR]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hfinal : S ≤ K * (B u u).re := by
    have h1 : 0 ≤ (B u u).re - 2 * (lam * S) + lam ^ 2 * (K * S) := by linarith
    have h2 : lam ^ 2 * (K * S) = lam * S := by
      have : lam ^ 2 * K = lam := by
        have : lam ^ 2 * K = lam * (lam * K) := by ring
        rw [this, hlamK, mul_one]
      calc lam ^ 2 * (K * S) = (lam ^ 2 * K) * S := by ring
        _ = lam * S := by rw [this]
    rw [h2] at h1
    have h3 : lam * S ≤ (B u u).re := by linarith
    have := mul_le_mul_of_nonneg_left h3 (le_of_lt hpos)
    calc S = K * (lam * S) := by rw [← mul_assoc, mul_comm K lam, hlamK, one_mul]
      _ ≤ K * (B u u).re := this
  exact hfinal


/-- **Approximate orthogonality forces approximate integrality of the energy.**  If the Gram
matrix of `e` is within `ε` of the identity, then the energy of an integer combination
`∑ᵢ mᵢ • eᵢ` differs from the integer `∑ᵢ mᵢ²` by at most `ε·(∑ᵢ |mᵢ|)²`.

For the logarithmic prime form and a family of primitive `L`-functions this says: an approximate
form of Selberg's orthogonality conjecture implies an approximate form of his normality
conjecture, with the error controlled by the `ℓ¹` norm of the multiplicity vector. -/
theorem energy_near_int_of_almost_orthonormal (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) (m : ι → ℤ) (ε : ℝ)
    (hgram : ∀ i j, ‖B (e i) (e j) - (if i = j then (1 : ℂ) else 0)‖ ≤ ε) :
    |(B (∑ i, ((m i : ℂ)) • e i) (∑ i, ((m i : ℂ)) • e i)).re - ∑ i, ((m i : ℝ)) ^ 2|
      ≤ ε * (∑ i, |(m i : ℝ)|) ^ 2 := by
  classical
  have hzero : ∀ z : V, B 0 z = 0 := by
    intro z; have := hsmul₁ 0 z z; simpa using this
  have hsum₁ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B (∑ i, f i • g i) z = ∑ i, f i * B (g i) z := by
    intro f g z
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty => simp [hzero]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd₁, hsmul₁, ih]
  have hsum₂ : ∀ (f : ι → ℂ) (g : ι → V) (z : V),
      B z (∑ i, f i • g i) = ∑ i, (starRingEnd ℂ) (f i) * B z (g i) := by
    intro f g z
    have h1 : B z (∑ i, f i • g i) = (starRingEnd ℂ) (B (∑ i, f i • g i) z) :=
      hconj (∑ i, f i • g i) z
    rw [h1, hsum₁, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ← hconj]
  set D : ι → ι → ℂ := fun i j => B (e i) (e j) - (if i = j then (1 : ℂ) else 0) with hD
  have hGram : ∀ i j, B (e i) (e j) = (if i = j then (1 : ℂ) else 0) + D i j := by
    intro i j; rw [hD]; ring
  have hconjm : ∀ i, (starRingEnd ℂ) ((m i : ℂ)) = (m i : ℂ) := by
    intro i
    simp
  have hexp : B (∑ i, ((m i : ℂ)) • e i) (∑ i, ((m i : ℂ)) • e i)
      = (∑ i, ((m i : ℂ)) ^ 2) + ∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j := by
    rw [hsum₁]
    have step : ∀ i : ι, (m i : ℂ) * B (e i) (∑ j, ((m j : ℂ)) • e j)
        = (m i : ℂ) ^ 2 + ∑ j, (m i : ℂ) * (m j : ℂ) * D i j := by
      intro i
      rw [hsum₂]
      have : ∀ j : ι, (starRingEnd ℂ) ((m j : ℂ)) * B (e i) (e j)
          = (if i = j then (m j : ℂ) else 0) + (m j : ℂ) * D i j := by
        intro j
        rw [hconjm j, hGram i j]
        by_cases h : i = j
        · simp [h]; ring
        · simp [h]
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, mul_add]
      congr 1
      · simp [sq]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_add_distrib]
  rw [hexp]
  have hre : ((∑ i, ((m i : ℂ)) ^ 2) + ∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j).re
      = (∑ i, ((m i : ℝ)) ^ 2) + (∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j).re := by
    rw [Complex.add_re]
    congr 1
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Complex.ofReal_intCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre]
  have hbound : ‖∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j‖ ≤ ε * (∑ i, |(m i : ℝ)|) ^ 2 := by
    have h1 : ‖∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j‖
        ≤ ∑ i, ∑ j, |(m i : ℝ)| * |(m j : ℝ)| * ε := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_mul]
      have hi : ‖(m i : ℂ)‖ = |(m i : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      have hj : ‖(m j : ℂ)‖ = |(m j : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      rw [hi, hj]
      exact mul_le_mul_of_nonneg_left (hgram i j) (by positivity)
    have h2 : ∑ i, ∑ j, |(m i : ℝ)| * |(m j : ℝ)| * ε = ε * (∑ i, |(m i : ℝ)|) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith [h1, h2.le, h2.ge]
  have := Complex.abs_re_le_norm (∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j)
  rw [add_sub_cancel_left]
  calc |(∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j).re|
      ≤ ‖∑ i, ∑ j, (m i : ℂ) * (m j : ℂ) * D i j‖ := this
    _ ≤ ε * (∑ i, |(m i : ℝ)|) ^ 2 := hbound


/-- **Integral Bessel.**  If the coefficients of `u` against an orthonormal family are rational
integers, then the sum of their squares is a non-negative integer bounded by the energy of `u`.

For the logarithmic prime form and the family of degree-one elements of the Selberg class — whose
coefficient vectors `p ↦ χ(p)p^(-iθ)` are orthonormal, and whose pairings against any `F` are the
integers `-ord_{1+iθ} F^{conj χ}` — this says that the prime energy dominates the total divisor mass
of all Dirichlet twists of `F` on the line `Re s = 1`, counted with multiplicity squared. -/
theorem integral_bessel_of_orthonormal (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    (hpsd : ∀ x, 0 ≤ (B x x).re)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) (u : V) (m : ι → ℤ)
    (horth : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (hint : ∀ i, B u (e i) = ((m i : ℤ) : ℂ)) :
    ∑ i, ((m i : ℝ)) ^ 2 ≤ (B u u).re := by
  have hb := bessel_of_orthonormal B hadd₁ hsmul₁ hconj hpsd e u horth
  refine le_trans (le_of_eq ?_) hb
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hint i]
  rw [show ‖((m i : ℤ) : ℂ)‖ = |(m i : ℝ)| from by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]]
  rw [sq_abs]


/-- **Cauchy–Schwarz for a positive semi-definite sesquilinear form.**  No definiteness is used, so
this applies to limits of positive forms such as the logarithmic prime form. -/
theorem cauchy_schwarz_psd (B : V → V → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (c : ℂ) (x y : V), B (c • x) y = c * B x y)
    (hconj : ∀ x y, B y x = (starRingEnd ℂ) (B x y))
    (hpsd : ∀ x, 0 ≤ (B x x).re) (x y : V) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re := by
  classical
  have hsub₁ : ∀ p q r : V, B (p - q) r = B p r - B q r := by
    intro p q r
    have h := hadd₁ (p - q) q r
    simp only [sub_add_cancel] at h
    linear_combination -h
  have hsub₂ : ∀ p q r : V, B p (q - r) = B p q - B p r := by
    intro p q r
    have h1 : B p (q - r) = (starRingEnd ℂ) (B (q - r) p) := hconj (q - r) p
    rw [h1, hsub₁, map_sub, ← hconj, ← hconj]
  have hsm₂ : ∀ (c : ℂ) (p q : V), B p (c • q) = (starRingEnd ℂ) c * B p q := by
    intro c p q
    have h1 : B p (c • q) = (starRingEnd ℂ) (B (c • q) p) := hconj (c • q) p
    rw [h1, hsmul₁, map_mul, ← hconj]
  set N : ℝ := ‖B x y‖ with hN
  set v : V := (B x y) • y with hv
  have hNsq : B x y * (starRingEnd ℂ) (B x y) = ((N ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hN]
  have hxv : B x v = ((N ^ 2 : ℝ) : ℂ) := by
    rw [hv, hsm₂, ← hNsq]; ring
  have hvx : B v x = ((N ^ 2 : ℝ) : ℂ) := by
    rw [hv, hsmul₁, hconj x y]; exact hNsq
  have hvv : B v v = ((N ^ 2 : ℝ) : ℂ) * B y y := by
    rw [hv, hsmul₁, hsm₂, ← mul_assoc, hNsq]
  clear_value v
  have hexpand : ∀ t : ℝ, B (x - (t : ℂ) • v) (x - (t : ℂ) • v)
      = B x x - (t : ℂ) * B v x - (t : ℂ) * B x v + (t : ℂ) ^ 2 * (B v v) := by
    intro t
    rw [hsub₁, hsub₂, hsub₂, hsmul₁, hsm₂, hsm₂, hsmul₁, Complex.conj_ofReal]
    ring
  have hkey : ∀ t : ℝ, 0 ≤ (B x x).re - 2 * t * N ^ 2 + t ^ 2 * (N ^ 2 * (B y y).re) := by
    intro t
    have hp := hpsd (x - (t : ℂ) • v)
    rw [hexpand t, hxv, hvx, hvv] at hp
    have hre : (B x x - (t : ℂ) * ((N ^ 2 : ℝ) : ℂ) - (t : ℂ) * ((N ^ 2 : ℝ) : ℂ)
        + (t : ℂ) ^ 2 * (((N ^ 2 : ℝ) : ℂ) * B y y)).re
        = (B x x).re - 2 * t * N ^ 2 + t ^ 2 * (N ^ 2 * (B y y).re) := by
      have hNre : ((N : ℂ) ^ 2).re = N ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
      have hNim : ((N : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
      have htre : ((t : ℂ) ^ 2).re = t ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
      have htim : ((t : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
      simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, hNre, hNim, htre, htim]
      ring
    rw [hre] at hp
    exact hp
  have hA : 0 ≤ (B y y).re := hpsd y
  rcases (norm_nonneg (B x y)).lt_or_eq with hNpos | hN0
  · have hNp : 0 < N := hNpos
    rcases eq_or_lt_of_le hA with hA0 | hApos
    · exfalso
      have hNp2 : (0:ℝ) < N ^ 2 := by positivity
      have h1 := hkey (((B x x).re + 1) / N ^ 2)
      rw [← hA0] at h1
      have hz : (((B x x).re + 1) / N ^ 2) ^ 2 * (N ^ 2 * 0) = 0 := by ring
      rw [hz, add_zero] at h1
      have hz2 : 2 * (((B x x).re + 1) / N ^ 2) * N ^ 2 = 2 * ((B x x).re + 1) := by
        field_simp
      rw [hz2] at h1
      linarith [h1, hpsd x]
    · have h := hkey (1 / (B y y).re)
      have hne : (B y y).re ≠ 0 := ne_of_gt hApos
      field_simp at h
      nlinarith [h, hApos, hNp]
  · have hNz : N = 0 := by rw [hN, ← hN0]
    rw [hNz]
    simpa using mul_nonneg (hpsd x) (hpsd y)

end HTGeometry
