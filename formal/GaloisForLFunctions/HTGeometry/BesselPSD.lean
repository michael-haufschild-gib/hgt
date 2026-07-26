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

end HTGeometry
