import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockBound
import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization

/-!
# The block inequality for `‖ζΨ‖²` on the displaced line

Summing the pair decomposition over a real mollifier `Ψ = Σ_{n ≤ N} a_n n^{-s}`:

  `∫ w ‖ζΨ‖² ≤ ‖ζ(1+2d)‖ · ‖∫ w χ(s₁)χ(s₂)‖ · S₂ + Σ_{h,k} |a_h a_k| ‖pairError_{hk}‖`,

where the direct main term `ζ(2σ₀)(∫w)S₁` has been dropped because `ζ(2σ₀) < 0`, `∫w ≥ 0` and
`S₁ = Σ a_h a_k gcd(h,k)^{2σ₀} (hk)^{-2σ₀} ≥ 0` (a gcd kernel form), and
`S₂ = Σ a_h a_k gcd(h,k)^{1+2d}/(hk) ≥ 0`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## The two main terms of a pair -/

/-- The reduced product `(h/g)(k/g)`, `g = gcd(h,k)`. -/
def reducedProd (h k : ℕ) : ℕ := (h / Nat.gcd h k) * (k / Nat.gcd h k)

def mainTerm₁ (d p q η : ℝ) (h k : ℕ) : ℂ :=
  ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * (((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ)
    * riemannZeta ((2 * (1 / 2 - d) : ℝ) : ℂ) * (∫ t, blockWindowC p q η t)

def mainTerm₂ (d p q η : ℝ) (h k : ℕ) : ℂ :=
  ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * (((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ)
    * riemannZeta ((1 + 2 * d : ℝ) : ℂ) * (∫ t, blockWindowC p q η t * chiPairWeight d t)

theorem gcd_facts {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < Nat.gcd h k ∧ 0 < h / Nat.gcd h k ∧ 0 < k / Nat.gcd h k
      ∧ Nat.Coprime (h / Nat.gcd h k) (k / Nat.gcd h k)
      ∧ h = Nat.gcd h k * (h / Nat.gcd h k) ∧ k = Nat.gcd h k * (k / Nat.gcd h k) := by
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh
  refine ⟨hg, Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h k)) hg,
    Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_right h k)) hg, Nat.coprime_div_gcd_div_gcd hg,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left h k)).symm,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right h k)).symm⟩

/-- The pair decomposition in terms of the two main terms. -/
theorem blockPair_eq_main {d x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (∑' P : ℕ × ℕ, directTerm d x p q η h k P) + (∑' P : ℕ × ℕ, dualTerm d x p q η h k P)
        - residueTerm d x p q η h k
      = mainTerm₁ d p q η h k + mainTerm₂ d p q η h k
        + pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k := by
  obtain ⟨hg, hh', hk', hcop, hhg, hkg⟩ := gcd_facts hh hk
  rw [blockPair_eq hd hd8 hx hη hL hpq hg hh' hk' hcop hhg hkg]
  unfold mainTerm₁ mainTerm₂ reducedProd
  ring

/-! ## The gcd sums -/

/-- `S₁ = Σ a_h a_k (hk)^{-σ₀} ((h/g)(k/g))^{-σ₀}`. -/
def gcdSum₁ (d : ℝ) (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, a h * a k
    * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)))

/-- `S₂ = Σ a_h a_k (hk)^{-σ₀} ((h/g)(k/g))^{-(½+d)}`. -/
def gcdSum₂ (d : ℝ) (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, a h * a k
    * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)))

theorem reducedProd_cast {h k : ℕ} (hh : 0 < h) :
    ((reducedProd h k : ℕ) : ℝ) = ((h : ℝ) * k) / ((Nat.gcd h k : ℝ)) ^ 2 := by
  unfold reducedProd
  have hg : (Nat.gcd h k : ℝ) ≠ 0 := by
    have := Nat.gcd_pos_of_pos_left k hh
    positivity
  push_cast [Nat.cast_div (Nat.gcd_dvd_left h k) hg, Nat.cast_div (Nat.gcd_dvd_right h k) hg]
  ring

theorem gcd_sq_rpow_neg {g : ℝ} (hg : 0 < g) (s : ℝ) : (g ^ 2) ^ (-s) = (g ^ (2 * s))⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le, ← Real.rpow_neg hg.le]
  congr 1
  push_cast
  ring

/-- The pair coefficient of `S₁` in gcd-kernel form. -/
theorem coeff₁_eq {d : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d))
      = ((h : ℝ) ^ (1 - 2 * (1 / 2 - d))) * ((k : ℝ) ^ (1 - 2 * (1 / 2 - d)))
        * (Nat.gcd h k : ℝ) ^ (2 * (1 / 2 - d)) / ((h : ℝ) * k) := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hgr : (0 : ℝ) < Nat.gcd h k := by exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  have hhk : (0 : ℝ) < (h : ℝ) * k := by positivity
  have e1 : (h : ℝ) ^ (1 - 2 * (1 / 2 - d))
      = h * ((h : ℝ) ^ (-(1 / 2 - d)) * (h : ℝ) ^ (-(1 / 2 - d))) := by
    rw [← Real.rpow_add hhr, show (1 - 2 * (1 / 2 - d) : ℝ) = 1 + (-(1 / 2 - d) + -(1 / 2 - d)) by ring,
      Real.rpow_add hhr, Real.rpow_one]
  have e2 : (k : ℝ) ^ (1 - 2 * (1 / 2 - d))
      = k * ((k : ℝ) ^ (-(1 / 2 - d)) * (k : ℝ) ^ (-(1 / 2 - d))) := by
    rw [← Real.rpow_add hkr, show (1 - 2 * (1 / 2 - d) : ℝ) = 1 + (-(1 / 2 - d) + -(1 / 2 - d)) by ring,
      Real.rpow_add hkr, Real.rpow_one]
  rw [reducedProd_cast hh, Real.div_rpow hhk.le (by positivity), gcd_sq_rpow_neg hgr,
    Real.mul_rpow hhr.le hkr.le, e1, e2, div_inv_eq_mul, eq_div_iff hhk.ne']
  ring

/-- The pair coefficient of `S₂` in gcd form. -/
theorem coeff₂_eq {d : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d))
      = (Nat.gcd h k : ℝ) ^ (1 + 2 * d) / ((h : ℝ) * k) := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hgr : (0 : ℝ) < Nat.gcd h k := by exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  have hhk : (0 : ℝ) < (h : ℝ) * k := by positivity
  have e1 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((h : ℝ) * k) ^ (-(1 / 2 + d)) = ((h : ℝ) * k)⁻¹ := by
    rw [← Real.rpow_add hhk, show (-(1 / 2 - d) + -(1 / 2 + d) : ℝ) = -1 by ring, Real.rpow_neg_one]
  have e2 : (Nat.gcd h k : ℝ) ^ (2 * (1 / 2 + d)) = (Nat.gcd h k : ℝ) ^ (1 + 2 * d) := by
    congr 1
    ring
  rw [reducedProd_cast hh, Real.div_rpow hhk.le (by positivity), gcd_sq_rpow_neg hgr, e2,
    ← mul_div_assoc, e1, div_inv_eq_mul, inv_mul_eq_div]

theorem gcdSum₁_nonneg {d : ℝ} (hd4 : d ≤ 1 / 4) (N : ℕ) (a : ℕ → ℝ) :
    0 ≤ gcdSum₁ d N a := by
  have h := Sieve.sum_gcd_rpow_div_nonneg (Finset.Icc 1 N)
    (fun m hm => (Finset.mem_Icc.mp hm).1)
    (fun n => a n * (n : ℝ) ^ (1 - 2 * (1 / 2 - d))) (s := 2 * (1 / 2 - d)) (by linarith)
  rw [Finset.sum_product] at h
  unfold gcdSum₁
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun k hk => ?_)
  rw [coeff₁_eq (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1]
  ring

theorem gcdSum₂_eq_gcd_form (d : ℝ) (N : ℕ) (a : ℕ → ℝ) :
    gcdSum₂ d N a = ∑ P ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      a P.1 * a P.2 * (Nat.gcd P.1 P.2 : ℝ) ^ (1 + 2 * d) / ((P.1 : ℝ) * P.2) := by
  rw [Finset.sum_product]
  unfold gcdSum₂
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun k hk => ?_
  rw [coeff₂_eq (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1]
  ring

theorem gcdSum₂_nonneg {d : ℝ} (hd0 : 0 ≤ d) (N : ℕ) (a : ℕ → ℝ) :
    0 ≤ gcdSum₂ d N a := by
  rw [gcdSum₂_eq_gcd_form]
  exact Sieve.sum_gcd_rpow_div_nonneg (Finset.Icc 1 N) (fun m hm => (Finset.mem_Icc.mp hm).1) a
    (by linarith)

/-! ## The sums of the main terms -/

theorem sum_mainTerm₁_eq {d p q η : ℝ} {N : ℕ} {b : ℕ → ℂ} {a : ℕ → ℝ}
    (hba : ∀ n ∈ Finset.Icc 1 N, b n = (a n : ℂ)) :
    ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k * mainTerm₁ d p q η h k
      = ((gcdSum₁ d N a : ℝ) : ℂ)
        * (riemannZeta ((2 * (1 / 2 - d) : ℝ) : ℂ) * (∫ t, blockWindowC p q η t)) := by
  unfold gcdSum₁
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hba h hh, hba k hk]
  unfold mainTerm₁
  push_cast
  ring

theorem sum_mainTerm₂_eq {d p q η : ℝ} {N : ℕ} {b : ℕ → ℂ} {a : ℕ → ℝ}
    (hba : ∀ n ∈ Finset.Icc 1 N, b n = (a n : ℂ)) :
    ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k * mainTerm₂ d p q η h k
      = ((gcdSum₂ d N a : ℝ) : ℂ)
        * (riemannZeta ((1 + 2 * d : ℝ) : ℂ) * (∫ t, blockWindowC p q η t * chiPairWeight d t)) := by
  unfold gcdSum₂
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hba h hh, hba k hk]
  unfold mainTerm₂
  push_cast
  ring

/-- The direct main term has nonpositive real part: `ζ(2σ₀) < 0`, `∫w ≥ 0`, `S₁ ≥ 0`. -/
theorem re_sum_mainTerm₁_nonpos {d p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) {N : ℕ} {b : ℕ → ℂ}
    {a : ℕ → ℝ} (hba : ∀ n ∈ Finset.Icc 1 N, b n = (a n : ℂ)) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k * mainTerm₁ d p q η h k).re ≤ 0 := by
  rw [sum_mainTerm₁_eq hba]
  obtain ⟨z, hz, hζ⟩ := riemannZeta_real_strip_neg (σ := 2 * (1 / 2 - d)) (by linarith) (by linarith)
  rw [hζ, integral_blockWindowC_eq_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  have h1 := gcdSum₁_nonneg hd4 N a
  have h2 := integral_blockWindow_nonneg p q η
  nlinarith [mul_nonneg h1 h2]

/-- The dual main term is at most `S₂ ‖ζ(1+2d)‖ ‖∫ w χχ‖` in real part. -/
theorem re_sum_mainTerm₂_le {d p q η : ℝ} (hd : 0 < d) {N : ℕ} {b : ℕ → ℂ}
    {a : ℕ → ℝ} (hba : ∀ n ∈ Finset.Icc 1 N, b n = (a n : ℂ)) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k * mainTerm₂ d p q η h k).re
      ≤ gcdSum₂ d N a * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC p q η t * chiPairWeight d t‖) := by
  rw [sum_mainTerm₂_eq hba]
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gcdSum₂_nonneg hd.le N a)]

/-! ## The block inequality -/

/-- **The block inequality.** -/
theorem integral_window_normSq_le {d x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {N : ℕ} {b : ℕ → ℂ} {a : ℕ → ℝ}
    (hba : ∀ n ∈ Finset.Icc 1 N, b n = (a n : ℂ)) :
    ∫ t, blockWindow p q η t * ‖riemannZeta (displacedLinePt d t)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2
      ≤ gcdSum₂ d N a * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC p q η t * chiPairWeight d t‖)
        + ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ‖b h‖ * ‖b k‖
          * ‖pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖ := by
  have hd4 : d ≤ 1 / 4 := by linarith
  have hbreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n := by
    intro n hn
    rw [hba n hn, Complex.conj_ofReal]
  -- the complex identity
  have hid := integral_window_normSq_eq hd hd4 hx hη hL hpq b N hbreal
  have hLc : ((∫ t, blockWindow p q η t * ‖riemannZeta (displacedLinePt d t)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ)
      = ∫ t, blockWindowC p q η t * ((‖riemannZeta (displacedLinePt d t)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ) := by
    have h0 : ((∫ t, blockWindow p q η t * ‖riemannZeta (displacedLinePt d t)
          * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ)
        = ∫ t, ((blockWindow p q η t * ‖riemannZeta (displacedLinePt d t)
          * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ) := integral_ofReal.symm
    rw [h0]
    congr 1
    funext t
    unfold blockWindowC
    push_cast
    ring
  rw [hid] at hLc
  have hre := congrArg Complex.re hLc
  rw [Complex.ofReal_re] at hre
  rw [hre]
  -- the pair decomposition
  have hpair : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      b h * b k * ((∑' P : ℕ × ℕ, directTerm d x p q η h k P)
        + (∑' P : ℕ × ℕ, dualTerm d x p q η h k P) - residueTerm d x p q η h k)
      = b h * b k * mainTerm₁ d p q η h k + b h * b k * mainTerm₂ d p q η h k
        + b h * b k * pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k := by
    intro h hh k hk
    rw [blockPair_eq_main hd hd8 hx hη hL hpq (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1]
    ring
  rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun k hk => hpair h hh k hk]
  simp only [Finset.sum_add_distrib, Complex.add_re]
  have h1 := re_sum_mainTerm₁_nonpos hd hd4 (p := p) (q := q) (η := η) hba
  have h2 := re_sum_mainTerm₂_le hd (p := p) (q := q) (η := η) hba
  have h3 : (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      b h * b k * pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k).re
      ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ‖b h‖ * ‖b k‖
          * ‖pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖ := by
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
  linarith

end RHTower.ZetaGateProductAFE

end
