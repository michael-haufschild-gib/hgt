import GaloisForLFunctions.PrimeTorusTheory.PrimeByPrimePaymentCannotUseTheGammaFactor
import GaloisForLFunctions.HTGeometry.DiscHolomorphicFixedPoint

/-!
# The certificate at rank one

The wall says that many returning prime coordinates pay for nothing. With a single coordinate there is no wall and the certificate is the Schur property, as over a function field.

**Theorem** (`exists_certificate_iff`, the two-point Pick criterion). For `S, z : X → 𝔻` there is a `2`-positive kernel `K` with

`1 − S(x) conj S(y) = (1 − z(x) conj z(y)) K(x, y)`

if and only if `ρ(S x, S y) ≤ ρ(z x, z y)` for all `x, y`, with `ρ` the pseudo-hyperbolic distance. `K` is unique: it is the quotient `pickKernel`.

**Corollary** (`twoPositive_pickKernel_comp`). By Schwarz–Pick, every holomorphic self-map `f` of the disc is paid by its coordinate.

**Rank one law** (`rank_one_law`). On `Re s > 0`, with one coordinate `q^{−s}`, the function `S(s) = f(q^{−s})` has a decomposition with no archimedean coordinate at all. It is periodic, with period `2π/log q`, so it tends to `0` vertically only if it vanishes: the hypothesis of the wall fails exactly where the certificate exists. A Gamma coordinate is needed only for functions that see absolute height.
-/

open Complex Filter Topology Metric Set

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

local notation "conj" => starRingEnd ℂ

open HTGeometry.DiscFixedPoint (mob)

/-- The real part of a Hermitian form with a real diagonal. -/
theorem re_form2_hermitian (a d : ℝ) (B u v : ℂ) :
    (form2 (a : ℂ) B (conj B) (d : ℂ) u v).re =
      ‖u‖ ^ 2 * a + ‖v‖ ^ 2 * d + 2 * (u * conj v * B).re := by
  have hu : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hv : v * conj v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc : v * conj u * conj B = conj (u * conj v * B) := by
    simp only [map_mul, Complex.conj_conj]
    ring
  unfold form2
  rw [hu, hv, hc, Complex.add_re, Complex.add_re, Complex.add_re, Complex.conj_re,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  ring

/-- `2xyb ≤ x²a + y²d` when `b² ≤ ad`. -/
theorem two_mul_mul_le {x y b a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (h : b ^ 2 ≤ a * d) :
    2 * (x * y * b) ≤ x ^ 2 * a + y ^ 2 * d := by
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    have hb2 : b = 0 := by
      have h0 : b ^ 2 ≤ 0 := by simpa using h
      nlinarith [sq_nonneg b]
    subst hb2
    simp only [mul_zero, zero_add]
    positivity
  · have hmul : 0 ≤ a * (x ^ 2 * a + y ^ 2 * d - 2 * (x * y * b)) := by
      have h1 := sq_nonneg (a * x - y * b)
      have h2 := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr h)
      nlinarith
    have := nonneg_of_mul_nonneg_right hmul ha0
    linarith

/-- A Hermitian form with `|B|² ≤ ad` is nonnegative. -/
theorem re_form2_nonneg_of_sq_le {a d : ℝ} {B : ℂ} (ha : 0 ≤ a) (hd : 0 ≤ d) (h : ‖B‖ ^ 2 ≤ a * d)
    (u v : ℂ) : 0 ≤ (form2 (a : ℂ) B (conj B) (d : ℂ) u v).re := by
  rw [re_form2_hermitian]
  have hre : -(‖u‖ * ‖v‖ * ‖B‖) ≤ (u * conj v * B).re := by
    have := Complex.abs_re_le_norm (u * conj v * B)
    rw [norm_mul, norm_mul, Complex.norm_conj] at this
    linarith [(abs_le.mp this).1]
  have key := two_mul_mul_le (x := ‖u‖) (y := ‖v‖) ha hd h
  linarith

/-- A nonnegative Hermitian form has `|B|² ≤ ad`. -/
theorem sq_le_of_re_form2_nonneg {a d : ℝ} {B : ℂ} (ha : 0 ≤ a)
    (h : ∀ u v : ℂ, 0 ≤ (form2 (a : ℂ) B (conj B) (d : ℂ) u v).re) : ‖B‖ ^ 2 ≤ a * d := by
  have hr : ∀ r : ℝ, 0 ≤ r ^ 2 * ‖B‖ ^ 2 * a + d - 2 * r * ‖B‖ ^ 2 := by
    intro r
    have := h (((-r : ℝ) : ℂ) * conj B) 1
    rw [re_form2_hermitian] at this
    have hB : conj B * B = ((‖B‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e1 : ((-r : ℝ) : ℂ) * conj B * conj 1 * B = ((-r * ‖B‖ ^ 2 : ℝ) : ℂ) := by
      rw [map_one, mul_one, mul_assoc, hB, Complex.ofReal_mul]
    rw [e1, Complex.ofReal_re, norm_mul, Complex.norm_conj, Complex.norm_real, norm_one, one_pow,
      one_mul, Real.norm_eq_abs, mul_pow, sq_abs] at this
    linarith
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    by_contra hcon
    have hb : 0 < ‖B‖ ^ 2 := by
      by_contra hb
      exact hcon (by simpa using (not_lt.mp hb))
    have := hr ((d + 1) / (2 * ‖B‖ ^ 2))
    have hB0 : ‖B‖ ≠ 0 := by
      intro h0
      simp [h0] at hb
    have e : 2 * ((d + 1) / (2 * ‖B‖ ^ 2)) * ‖B‖ ^ 2 = d + 1 := by
      field_simp
    rw [mul_zero, e] at this
    linarith
  · have := hr (1 / a)
    have e : (1 / a) ^ 2 * ‖B‖ ^ 2 * a + d - 2 * (1 / a) * ‖B‖ ^ 2 = (a * d - ‖B‖ ^ 2) / a := by
      field_simp
      ring
    rw [e] at this
    have h2 := (div_nonneg_iff.mp this).resolve_right (fun h => not_le.mpr ha0 h.2)
    linarith [h2.1]

theorem norm_one_sub_mul_conj (a b : ℂ) : ‖1 - a * conj b‖ = ‖1 - conj a * b‖ := by
  rw [← Complex.norm_conj (1 - conj a * b)]
  simp only [map_sub, map_one, map_mul, Complex.conj_conj]

/-- The pseudo-hyperbolic comparison, without the Möbius maps. -/
theorem norm_mob_le_iff {a b p q : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ‖mob a b‖ ≤ ‖mob p q‖ ↔
      (1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2) * ‖1 - conj a * b‖ ^ 2 ≤
        (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) * ‖1 - conj p * q‖ ^ 2 := by
  have hne1 := HTGeometry.DiscFixedPoint.one_sub_conj_mul_ne_zero ha hb.le
  have hne2 := HTGeometry.DiscFixedPoint.one_sub_conj_mul_ne_zero hp hq.le
  have h1 := HTGeometry.DiscFixedPoint.normSq_one_sub_sub_normSq a b
  have h2 := HTGeometry.DiscFixedPoint.normSq_one_sub_sub_normSq p q
  simp only [Complex.normSq_eq_norm_sq] at h1 h2
  unfold mob
  rw [norm_div, norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2),
    ← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow, ← h1, ← h2]
  constructor <;> intro h <;> linarith

variable {X : Type*} {S z : X → ℂ}

/-- The quotient kernel of `S` over the coordinate `z`. -/
def pickKernel (S z : X → ℂ) (x y : X) : ℂ :=
  (1 - S x * conj (S y)) / (1 - z x * conj (z y))

/-- The diagonal of the quotient kernel. -/
def pickDiag (S z : X → ℂ) (x : X) : ℝ := (1 - ‖S x‖ ^ 2) / (1 - ‖z x‖ ^ 2)

theorem pickKernel_self (S z : X → ℂ) (x : X) : pickKernel S z x x = (pickDiag S z x : ℂ) := by
  unfold pickKernel pickDiag
  rw [one_sub_mul_conj, one_sub_mul_conj, Complex.ofReal_div]

theorem pickKernel_symm (S z : X → ℂ) (x y : X) :
    pickKernel S z y x = conj (pickKernel S z x y) := by
  unfold pickKernel
  simp only [map_div₀, map_sub, map_one, map_mul, Complex.conj_conj]
  rw [mul_comm (S y), mul_comm (z y)]

theorem one_sub_mul_conj_ne_zero {p q : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) : 1 - p * conj q ≠ 0 := by
  rw [← norm_pos_iff, norm_one_sub_mul_conj, norm_pos_iff]
  exact HTGeometry.DiscFixedPoint.one_sub_conj_mul_ne_zero hp hq.le

/-- The determinant of the quotient kernel is the pseudo-hyperbolic comparison. -/
theorem sq_norm_pickKernel_le_iff (hS : ∀ x, ‖S x‖ < 1) (hz : ∀ x, ‖z x‖ < 1) (x y : X) :
    ‖pickKernel S z x y‖ ^ 2 ≤ pickDiag S z x * pickDiag S z y ↔
      ‖mob (S x) (S y)‖ ≤ ‖mob (z x) (z y)‖ := by
  have hP : 0 < ‖1 - z x * conj (z y)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (one_sub_mul_conj_ne_zero (hz x) (hz y))) 2
  have hd : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  have hβ := mul_pos (hd _ (hz x)) (hd _ (hz y))
  rw [norm_mob_le_iff (hS x) (hS y) (hz x) (hz y)]
  unfold pickKernel pickDiag
  rw [norm_div, div_pow, div_mul_div_comm, div_le_div_iff₀ hP hβ, norm_one_sub_mul_conj,
    norm_one_sub_mul_conj]
  constructor <;> intro h <;> linarith

theorem pickDiag_nonneg (hS : ∀ x, ‖S x‖ < 1) (hz : ∀ x, ‖z x‖ < 1) (x : X) : 0 ≤ pickDiag S z x := by
  have hd : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  exact (div_pos (hd _ (hS x)) (hd _ (hz x))).le

/-- The quotient kernel is `2`-positive exactly when `S` contracts the pseudo-hyperbolic distance of `z`. -/
theorem twoPositive_pickKernel_iff (hS : ∀ x, ‖S x‖ < 1) (hz : ∀ x, ‖z x‖ < 1) :
    TwoPositive (pickKernel S z) ↔ ∀ x y, ‖mob (S x) (S y)‖ ≤ ‖mob (z x) (z y)‖ := by
  have hform : ∀ x y u v, form2 (pickKernel S z x x) (pickKernel S z x y) (pickKernel S z y x)
      (pickKernel S z y y) u v = form2 (pickDiag S z x : ℂ) (pickKernel S z x y)
        (conj (pickKernel S z x y)) (pickDiag S z y : ℂ) u v := fun x y u v => by
    rw [pickKernel_self, pickKernel_self, pickKernel_symm S z x y]
  constructor
  · intro h x y
    refine (sq_norm_pickKernel_le_iff hS hz x y).mp (sq_le_of_re_form2_nonneg (pickDiag_nonneg hS hz x) ?_)
    intro u v
    rw [← hform]
    exact h x y u v
  · intro h x y u v
    rw [hform]
    exact re_form2_nonneg_of_sq_le (pickDiag_nonneg hS hz x) (pickDiag_nonneg hS hz y)
      ((sq_norm_pickKernel_le_iff hS hz x y).mpr (h x y)) u v

/-- **The two-point Pick criterion.** A single coordinate pays for `S` with a `2`-positive kernel exactly when `S` contracts its pseudo-hyperbolic distance. The kernel is forced to be the quotient. -/
theorem exists_certificate_iff (hS : ∀ x, ‖S x‖ < 1) (hz : ∀ x, ‖z x‖ < 1) :
    (∃ K : X → X → ℂ, TwoPositive K ∧ ∀ x y, 1 - S x * conj (S y) = (1 - z x * conj (z y)) * K x y) ↔
      ∀ x y, ‖mob (S x) (S y)‖ ≤ ‖mob (z x) (z y)‖ := by
  rw [← twoPositive_pickKernel_iff hS hz]
  constructor
  · rintro ⟨K, hK, heq⟩
    have : K = pickKernel S z := by
      funext x y
      unfold pickKernel
      rw [heq, mul_comm, mul_div_assoc, div_self (one_sub_mul_conj_ne_zero (hz x) (hz y)), mul_one]
    exact this ▸ hK
  · intro h
    refine ⟨_, h, fun x y => ?_⟩
    unfold pickKernel
    rw [mul_div_cancel₀ _ (one_sub_mul_conj_ne_zero (hz x) (hz y))]

/-- **Schwarz–Pick is the certificate.** Every holomorphic self-map of the disc is paid by its coordinate. -/
theorem twoPositive_pickKernel_comp {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) (hz : ∀ x, ‖z x‖ < 1) :
    TwoPositive (pickKernel (fun x => f (z x)) z) := by
  have hzb : ∀ x, z x ∈ ball (0 : ℂ) 1 := fun x => mem_ball_zero_iff.mpr (hz x)
  refine (twoPositive_pickKernel_iff (fun x => mem_ball_zero_iff.mp (hm (hzb x))) hz).mpr fun x y => ?_
  exact HTGeometry.DiscFixedPoint.norm_mob_le_of_mapsTo hd hm (hzb x) (hzb y)

/-- The coordinate `q^{−s}`. -/
def rankOneCoord (q : ℕ) (s : HalfPlane) : ℂ := (q : ℂ) ^ (-s.1)

theorem norm_rankOneCoord_lt {q : ℕ} (hq : 2 ≤ q) (s : HalfPlane) : ‖rankOneCoord q s‖ < 1 := by
  unfold rankOneCoord
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < q)) (by simpa using s.2)

/-- The coordinate `q^{−s}` has period `2π/log q`. -/
theorem rankOneCoord_period {q : ℕ} (hq : 2 ≤ q) (s : HalfPlane) (n : ℕ) :
    rankOneCoord q (vshift s (n * (2 * Real.pi / Real.log q))) = rankOneCoord q s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hlog : Real.log q ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < q))).ne'
  have hlogC : ((Real.log q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  unfold rankOneCoord vshift
  simp only
  rw [neg_add, Complex.cpow_add _ _ hq0]
  have hone : (q : ℂ) ^ (-(((n * (2 * Real.pi / Real.log q) : ℝ) : ℂ) * I)) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
    have e : ((Real.log q : ℝ) : ℂ) * -(((n * (2 * Real.pi / Real.log q) : ℝ) : ℂ) * I) =
        -((n : ℂ) * (2 * Real.pi * I)) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
      field_simp
    rw [e, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]
  rw [hone, mul_one]

/-- **The certificate on a half-plane at rank one.** `f(q^{−s})` is paid by `q^{−s}` alone, with no archimedean coordinate. -/
def rankOneDecomposition {q : ℕ} (hq : 2 ≤ q) {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) :
    AglerDecomposition (fun s => f (rankOneCoord q s)) (fun _ => 0) (fun _ : Unit => rankOneCoord q) where
  K := fun _ => pickKernel (fun s => f (rankOneCoord q s)) (rankOneCoord q)
  K₀ := fun _ _ => 0
  psd := fun _ => twoPositive_pickKernel_comp hd hm (norm_rankOneCoord_lt hq)
  psd₀ := fun _ _ u v => by simp [form2]
  eq := fun x y => by
    simp only [Fintype.univ_unit, Finset.sum_singleton, mul_zero, add_zero]
    unfold pickKernel
    rw [mul_div_cancel₀ _ (one_sub_mul_conj_ne_zero (norm_rankOneCoord_lt hq x) (norm_rankOneCoord_lt hq y))]

/-- **The rank one law.** At one coordinate every Schur function has a certificate with no Gamma factor, and it decays vertically only if it vanishes: the wall has nothing to say there. -/
theorem rank_one_law {q : ℕ} (hq : 2 ≤ q) {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) :
    Nonempty (AglerDecomposition (fun s => f (rankOneCoord q s)) (fun _ => 0)
      (fun _ : Unit => rankOneCoord q)) ∧
      ∀ s, Tendsto (fun τ => f (rankOneCoord q (vshift s τ))) atTop (𝓝 0) → f (rankOneCoord q s) = 0 := by
  refine ⟨⟨rankOneDecomposition hq hd hm⟩, fun s hs => ?_⟩
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hτ : Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi / Real.log q)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  have hcomp := hs.comp hτ
  have hconst : (fun τ => f (rankOneCoord q (vshift s τ))) ∘
      (fun n : ℕ => (n : ℝ) * (2 * Real.pi / Real.log q)) = fun _ => f (rankOneCoord q s) := by
    funext n
    simp only [Function.comp, rankOneCoord_period hq s n]
  rw [hconst] at hcomp
  exact tendsto_nhds_unique tendsto_const_nhds hcomp

end

end GaloisForLFunctions.PrimeTorusTheory
