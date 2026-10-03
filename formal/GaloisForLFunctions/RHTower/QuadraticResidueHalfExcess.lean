import GaloisForLFunctions.RHTower.DirichletAbel
import GaloisForLFunctions.RHTower.SawtoothFourierSeries
import GaloisForLFunctions.RHTower.QuadraticGaussSumSign

/-!
# Dirichlet's excess of quadratic residues

For a prime `p ≡ 3 (mod 4)` and `χ = (·/p)`:

* `sinZeta(x, 1) = π(1/2 − x)` and `ζ_odd(x, 0) = 1/2 − x` for `0 < x < 1` (`hurwitzZetaOdd_zero`):
  the boundary series `Σ e(nx)/n` converges to `expZeta(x, 1)` (Abel summation), and its sine part
  is the sawtooth Fourier series;
* hence `L(χ, 0) = −(1/p) Σ_{r<p} r χ(r)` (`LFunction_legendre_zero`);
* the functional equation with Gauss's `τ(χ) = i√p` gives `L(χ, 0) = (√p/π) L(χ, 1)`;
* `L(χ, 1) > 0`: for real `t > 1` the Euler product is a positive real, and `L(χ, 1) ≠ 0`;
* the elementary identity `(1 − 2χ(2)) Σ_{r<p} r χ(r) = p χ(2) Σ_{0<r<p/2} χ(r)`.

Together: **`Σ_{0<r<p/2} (r/p) > 0`** (`sum_legendreSym_half_pos`).
-/

open Complex HurwitzZeta Filter Topology Finset

namespace GaloisForLFunctions.RHTower.QuadraticResidueExcess

theorem exp_two_pi_I_mul_ne_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Complex.exp (2 * ↑Real.pi * I * x) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat,
    intCast_re, intCast_im] at him
  have hpi := Real.pi_pos
  have : x = n := by nlinarith
  have h0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) < 1 := by linarith
  have : (0 : ℤ) < n := by exact_mod_cast h0
  have : n < (1 : ℤ) := by exact_mod_cast h1
  omega

theorem coe_ne_zero_of_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ((x : ℝ) : UnitAddCircle) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  have : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

/-- The partial sums of `Σ e(nx)/n` converge to `expZeta(x, 1)`. -/
theorem tendsto_sum_exp_div_expZeta_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ => ∑ i ∈ range n,
        (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ)) * _root_.RHTower.expCoeff x i)
      atTop (𝓝 (expZeta ((x : ℝ) : UnitAddCircle) 1)) := by
  have ha := exp_two_pi_I_mul_ne_one hx0 hx1
  have h := _root_.RHTower.tendsto_abelDirichlet
    (_root_.RHTower.norm_coeffPartial_expCoeff_le ha) (s := 1) (by norm_num)
  rwa [_root_.RHTower.abelDirichlet_eq_expZeta (coe_ne_zero_of_mem_Ioo hx0 hx1) ha
    (by norm_num)] at h

/-- **`sinZeta(x, 1) = π(1/2 − x)`** for `0 < x < 1`. -/
theorem sinZeta_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    sinZeta ((x : ℝ) : UnitAddCircle) 1 = Real.pi * (1 / 2 - x) := by
  have hp := tendsto_sum_exp_div_expZeta_one hx0 hx1
  have hm := tendsto_sum_exp_div_expZeta_one (x := 1 - x) (by linarith) (by linarith)
  -- `expZeta(x) − expZeta(1 − x) = 2i sinZeta(x)`
  have hneg : (((1 - x : ℝ)) : UnitAddCircle) = -((x : ℝ) : UnitAddCircle) := by
    rw [show (1 - x : ℝ) = -x + 1 by ring, AddCircle.coe_add, AddCircle.coe_period, add_zero,
      AddCircle.coe_neg]
  have hdiff : expZeta ((x : ℝ) : UnitAddCircle) 1 - expZeta (((1 - x : ℝ)) : UnitAddCircle) 1 =
      2 * I * sinZeta ((x : ℝ) : UnitAddCircle) 1 := by
    rw [hneg, expZeta, expZeta, cosZeta_neg, sinZeta_neg]; ring
  have hlim := (hp.sub hm).div_const (2 * I)
  rw [hdiff, show 2 * I * sinZeta ((x : ℝ) : UnitAddCircle) 1 / (2 * I) =
    sinZeta ((x : ℝ) : UnitAddCircle) 1 by field_simp] at hlim
  -- the left side is the sawtooth series at `θ = 2πx`
  have hθ : 2 * Real.pi * x ∈ Set.Ioo 0 (2 * Real.pi) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hsaw := GaloisForLFunctions.RHTower.tendsto_sum_sawtoothSine hθ
  rw [GaloisForLFunctions.RHTower.sawWave_eq_of_mem_Ioo hθ] at hsaw
  have hsaw' := ((Complex.continuous_ofReal.tendsto _).comp hsaw).comp (tendsto_add_atTop_nat 1)
  have hterm : ∀ n : ℕ, (∑ i ∈ range n,
      (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ)) * _root_.RHTower.expCoeff x i -
      ∑ i ∈ range n, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ)) * _root_.RHTower.expCoeff (1 - x) i) /
        (2 * I) = (((∑ m ∈ range (n + 1), Real.sin ((m : ℝ) * (2 * Real.pi * x)) / (m : ℝ)) : ℝ) :
          ℂ) := by
    intro n
    rw [sum_range_succ', ← sum_sub_distrib, sum_div]
    push_cast
    simp only [zero_mul, div_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [_root_.RHTower.expCoeff]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    set θ : ℂ := ((i : ℂ) + 1) * (2 * ↑Real.pi * ↑x) with hθdef
    have hE1 : ((i + 1 : ℕ) : ℂ) * (2 * ↑Real.pi * I * ↑x) = θ * I := by
      rw [hθdef]; push_cast; ring
    have hE2 : Complex.exp (((i + 1 : ℕ) : ℂ) * (2 * ↑Real.pi * I * ↑(1 - x))) =
        Complex.exp (-(θ * I)) := by
      rw [show ((i + 1 : ℕ) : ℂ) * (2 * ↑Real.pi * I * ↑(1 - x)) =
          ((i + 1 : ℕ) : ℂ) * (2 * ↑Real.pi * I) + -(θ * I) by rw [hθdef]; push_cast; ring,
        Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, one_mul]
    have h1 : ((i : ℂ) + 1) ^ (-(1 : ℂ)) = 1 / ((i : ℂ) + 1) := by
      rw [cpow_neg_one, one_div]
    rw [hE1, hE2, h1, Complex.sin]
    have hi : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hlim' := hlim.congr fun n => hterm n
  have huniq := tendsto_nhds_unique hlim' hsaw'
  rw [huniq]
  push_cast
  ring

/-- **`ζ_odd(x, 0) = 1/2 − x`** for `0 < x < 1` (the case `k = 0` of the Bernoulli values). -/
theorem hurwitzZetaOdd_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    hurwitzZetaOdd ((x : ℝ) : UnitAddCircle) 0 = 1 / 2 - x := by
  have h := hurwitzZetaOdd_one_sub ((x : ℝ) : UnitAddCircle) (s := 1) (fun n => by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  rw [sub_self, sinZeta_one hx0 hx1] at h
  rw [h]
  simp only [Gamma_one, mul_one, cpow_neg_one]
  rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_div_two]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-! ### The Legendre character as an odd Dirichlet character -/

open GaloisForLFunctions.RHTower.HalfWeight

variable {p : ℕ} [hp : Fact p.Prime]

theorem legendreC_natCast (r : ℕ) : legendreC p (r : ZMod p) = (legendreSym p r : ℂ) := by
  simp [legendreC, legendreSym]

theorem legendreC_neg_one (hp4 : p % 4 = 3) : legendreC p (-1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  have h := legendreSym.at_neg_one (p := p) hp2
  rw [ZMod.χ₄_nat_three_mod_four hp4] at h
  have : legendreC p (-1) = (legendreSym p (-1) : ℂ) := by simp [legendreC, legendreSym]
  rw [this, h]; push_cast; ring

theorem legendreC_neg (hp4 : p % 4 = 3) (a : ZMod p) : legendreC p (-a) = -legendreC p a := by
  rw [show -a = -1 * a by ring, map_mul, legendreC_neg_one hp4]; ring

theorem legendreC_ne_one (hp4 : p % 4 = 3) : legendreC p ≠ 1 := by
  intro h
  have := legendreC_neg_one (p := p) hp4
  rw [h, MulChar.one_apply (isUnit_one.neg)] at this
  norm_num at this

theorem legendreC_isPrimitive (hp4 : p % 4 = 3) :
    DirichletCharacter.IsPrimitive (show DirichletCharacter ℂ p from legendreC p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp (DirichletCharacter.conductor_dvd_level
    (legendreC p : DirichletCharacter ℂ p)) with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) (legendreC_ne_one hp4)
  · exact h

theorem legendreC_inv_apply (a : ZMod p) : (legendreC p)⁻¹ a = legendreC p a := by
  rw [MulChar.inv_apply']
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h1 : legendreC p a * legendreC p a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    have h2 : legendreC p a * legendreC p a = 1 := by
      have : legendreC p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by simp [legendreC]
      rw [this, ← Int.cast_mul, ← sq, quadraticChar_sq_one ha]; simp
    have hne : legendreC p a ≠ 0 := fun h0 => by rw [h0, zero_mul] at h2; exact zero_ne_one h2
    exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-! ### `L(χ, 0)` as a finite sum -/

/-- `L(χ, 0) = −(1/p) Σ_{r<p} r (r/p)`. -/
theorem LFunction_legendre_zero (hp4 : p % 4 = 3) :
    ZMod.LFunction (legendreC p : ZMod p → ℂ) 0 =
      -(1 / (p : ℂ)) * ∑ r ∈ range p, (r : ℂ) * legendreSym p r := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hodd : Function.Odd (legendreC p : ZMod p → ℂ) := fun a => legendreC_neg hp4 a
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [ZMod.LFunction_def_odd hodd, neg_zero, cpow_zero, one_mul]
  have hterm : ∀ j : ZMod p, legendreC p j * hurwitzZetaOdd (ZMod.toAddCircle j) 0 =
      legendreC p j * (1 / 2) - (1 / (p : ℂ)) * ((j.val : ℂ) * legendreC p j) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · have h0 : legendreC p 0 = 0 := by simp [legendreC]
      simp [h0]
    · have hv0 : 0 < j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
      have hvp : j.val < p := ZMod.val_lt j
      rw [ZMod.toAddCircle_apply, hurwitzZetaOdd_zero
        (div_pos (by exact_mod_cast hv0) (by exact_mod_cast hp.out.pos))
        ((div_lt_one (by exact_mod_cast hp.out.pos)).mpr (by exact_mod_cast hvp))]
      push_cast
      field_simp
  rw [sum_congr rfl fun j _ => hterm j, sum_sub_distrib, ← sum_mul,
    MulChar.sum_eq_zero_of_ne_one (legendreC_ne_one hp4), zero_mul, zero_sub, ← mul_sum, neg_mul]
  congr 2
  -- reindex `ZMod p ≃ range p`
  refine (sum_nbij' (fun j : ZMod p => j.val) (fun r => (r : ZMod p)) ?_ ?_ ?_ ?_ ?_)
  · intro j _; exact mem_range.mpr (ZMod.val_lt j)
  · intro r _; exact mem_univ _
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro r hr; exact ZMod.val_cast_of_lt (mem_range.mp hr)
  · intro j _
    rw [← legendreC_natCast, ZMod.natCast_zmod_val]

/-! ### The half-sum identity -/

theorem sum_range_two_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (P : ℕ) :
    ∑ j ∈ range (2 * P), f j = ∑ i ∈ range P, (f (2 * i) + f (2 * i + 1)) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [show 2 * (P + 1) = 2 * P + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- `(1 − 2χ(2)) Σ_{a<p} a χ(a) = p χ(2) Σ_{0<a<p/2} χ(a)` for odd `χ`. -/
theorem half_sum_identity (hp4 : p % 4 = 3) :
    (1 - 2 * legendreSym p 2) * ∑ a ∈ range p, (a : ℤ) * legendreSym p a =
      p * legendreSym p 2 * ∑ a ∈ range ((p + 1) / 2), legendreSym p a := by
  have hp2 : p ≠ 2 := by omega
  have hneg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp4]
  obtain ⟨h, hh⟩ : ∃ h, p = 2 * h + 1 := ⟨p / 2, by omega⟩
  have hhalf : (p + 1) / 2 = h + 1 := by omega
  rw [hhalf]
  -- reflection `χ(p − c) = −χ(c)`
  have hrefl : ∀ c : ℕ, c ≤ p → legendreSym p ((p - c : ℕ) : ℤ) = -legendreSym p c := by
    intro c hc
    rw [legendreSym.mod, Nat.cast_sub hc]
    have : ((p : ℤ) - c) % p = (-(c : ℤ)) % p := by
      rw [show (p : ℤ) - c = -c + p * 1 by ring, Int.add_mul_emod_self_left]
    rw [this, ← legendreSym.mod, show -(c : ℤ) = -1 * c by ring, legendreSym.mul, hneg]; ring
  have hp0 : legendreSym p (p : ℤ) = 0 := by
    rw [legendreSym.eq_zero_iff]; simp
  have hχ0 : legendreSym p 0 = 0 := by
    rw [legendreSym.eq_zero_iff]; simp
  set χ2 := legendreSym p 2
  set M := ∑ c ∈ range (h + 1), (c : ℤ) * legendreSym p c
  set S := ∑ c ∈ range (h + 1), legendreSym p (c : ℤ)
  set T := ∑ a ∈ range p, (a : ℤ) * legendreSym p a
  -- `T = 2M − pS` (pair `a` with `p − a`)
  have h1 : T = 2 * M - p * S := by
    have e : T = M +
        ∑ i ∈ range h, ((h + 1 + i : ℕ) : ℤ) * legendreSym p ((h + 1 + i : ℕ) : ℤ) := by
      simp only [T, M]
      rw [show range p = range ((h + 1) + h) by congr 1; omega, sum_range_add]
    rw [e]
    have e2 : ∑ i ∈ range h, ((h + 1 + i : ℕ) : ℤ) * legendreSym p ((h + 1 + i : ℕ) : ℤ) =
        ∑ i ∈ range h, -((p : ℤ) - ((h - i : ℕ) : ℤ)) * legendreSym p ((h - i : ℕ) : ℤ) := by
      refine sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      have hx : h + 1 + i = p - (h - i) := by omega
      rw [hx, hrefl _ (by omega), Nat.cast_sub (by omega : h - i ≤ p)]
      ring
    have e3 : ∑ i ∈ range h, -((p : ℤ) - ((h - i : ℕ) : ℤ)) * legendreSym p ((h - i : ℕ) : ℤ) =
        ∑ c ∈ range (h + 1), -((p : ℤ) - (c : ℤ)) * legendreSym p (c : ℤ) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, hχ0, mul_zero, add_zero]
      conv_lhs => rw [← sum_range_reflect]
      refine sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      rw [show h - (h - 1 - i) = i + 1 by omega]
    rw [e2, e3]
    simp only [M, S, neg_mul, sub_mul, sum_neg_distrib, sum_sub_distrib, ← mul_sum]
    ring
  -- `T = χ(2)(4M − pS)` (even/odd split)
  have h2 : T = χ2 * (4 * M - p * S) := by
    have e : T = ∑ a ∈ range (2 * (h + 1)), (a : ℤ) * legendreSym p a := by
      simp only [T]
      rw [show 2 * (h + 1) = p + 1 by omega, Finset.sum_range_succ, hp0, mul_zero, add_zero]
    rw [e, sum_range_two_mul', sum_add_distrib]
    have heven : ∑ c ∈ range (h + 1), ((2 * c : ℕ) : ℤ) * legendreSym p ((2 * c : ℕ) : ℤ) =
        χ2 * (2 * M) := by
      simp only [M, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      push_cast; rw [legendreSym.mul]; ring
    have hodd' : ∑ c ∈ range (h + 1), ((2 * c + 1 : ℕ) : ℤ) * legendreSym p ((2 * c + 1 : ℕ) : ℤ) =
        χ2 * (2 * M - p * S) := by
      rw [← sum_range_reflect]
      have : ∀ c ∈ range (h + 1), ((2 * (h + 1 - 1 - c) + 1 : ℕ) : ℤ) *
          legendreSym p ((2 * (h + 1 - 1 - c) + 1 : ℕ) : ℤ) =
          χ2 * (2 * (c * legendreSym p c) - p * legendreSym p c) := by
        intro c hc
        rw [mem_range] at hc
        have hx : 2 * (h + 1 - 1 - c) + 1 = p - 2 * c := by omega
        rw [hx, hrefl _ (by omega), Nat.cast_sub (by omega : 2 * c ≤ p)]
        push_cast
        rw [legendreSym.mul]
        ring
      rw [sum_congr rfl this, ← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum]
    rw [heven, hodd']
    ring
  -- solve
  rw [h2] at h1 ⊢
  have hT : T = χ2 * (4 * M - p * S) := h2
  linear_combination (-(2 : ℤ)) * χ2 * h1 + 0 * hT

/-! ### The functional equation at `s = 1` -/

theorem LFunction_const_mul_fun {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **`L(χ, 0) = (√p/π) L(χ, 1)`** for `p ≡ 3 (mod 4)` (Gauss: `τ(χ) = i√p`). -/
theorem LFunction_legendre_zero_eq (hp4 : p % 4 = 3) :
    ZMod.LFunction (legendreC p : ZMod p → ℂ) 0 =
      ((Real.sqrt p / Real.pi : ℝ) : ℂ) * ZMod.LFunction (legendreC p : ZMod p → ℂ) 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have h0 : legendreC p 0 = 0 := by simp [legendreC]
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -n := fun n h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hFE := ZMod.LFunction_one_sub (legendreC p : ZMod p → ℂ) hs (Or.inl h0)
  rw [sub_self] at hFE
  set τ := gaussSum (legendreC p) ZMod.stdAddChar with hτ
  have hτv : τ = I * (Real.sqrt p : ℂ) := by
    rw [hτ, gaussSum_legendre p hp2, gaussQuad_of_mod_four_eq_three p hp4]
  have hprim := legendreC_isPrimitive (p := p) hp4
  have hF : ZMod.dft (legendreC p : ZMod p → ℂ) = fun k => -τ * legendreC p k := by
    funext k
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum k]
    change (legendreC p)⁻¹ (-k) * τ = _
    rw [legendreC_inv_apply, legendreC_neg hp4]
    ring
  have hFneg : ZMod.dft (fun x => legendreC p (-x)) = fun k => τ * legendreC p k := by
    have : (fun x => legendreC p (-x)) = -(legendreC p : ZMod p → ℂ) := by
      funext x; rw [legendreC_neg hp4]; rfl
    rw [this, map_neg, hF]
    funext k
    simp
  rw [hF, hFneg, LFunction_const_mul_fun, LFunction_const_mul_fun] at hFE
  have he1 : Complex.exp (↑Real.pi * I * 1 / 2) = I := by
    rw [show (↑Real.pi : ℂ) * I * 1 / 2 = ↑Real.pi / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
  have he2 : Complex.exp (-↑Real.pi * I * 1 / 2) = -I := by
    rw [show -(↑Real.pi : ℂ) * I * 1 / 2 = -(↑Real.pi / 2 * I) by ring, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  rw [he1, he2, cpow_zero, one_mul, Complex.Gamma_one, mul_one, cpow_neg_one, hτv] at hFE
  rw [hFE]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Positivity of `L(χ, 1)` -/

theorem legendreC_real (a : ZMod p) : ∃ c : ℝ, -1 ≤ c ∧ c ≤ 1 ∧ legendreC p a = c := by
  refine ⟨(quadraticChar (ZMod p) a : ℝ), ?_, ?_, by simp [legendreC]⟩
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> norm_num
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> norm_num

/-- For real `t > 1`, `L(χ, t)` is a positive real (Euler product). -/
theorem LFunction_legendre_real_pos {t : ℝ} (ht : 1 < t) :
    ∃ r : ℝ, 0 < r ∧ ZMod.LFunction (legendreC p : ZMod p → ℂ) t = r := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hts : 1 < (t : ℂ).re := by simpa using ht
  have hL : ZMod.LFunction (legendreC p : ZMod p → ℂ) t =
      Complex.exp (∑' q : Nat.Primes, -Complex.log (1 - (legendreC p : DirichletCharacter ℂ p) q *
        ((q : ℕ) : ℂ) ^ (-(t : ℂ)))) :=
    (DirichletCharacter.LFunction_eq_LSeries (legendreC p : DirichletCharacter ℂ p) hts).trans
      (DirichletCharacter.LSeries_eulerProduct_exp_log
        (legendreC p : DirichletCharacter ℂ p) hts).symm
  -- each Euler factor is the logarithm of a positive real
  have hterm : ∀ q : Nat.Primes, ∃ x : ℝ,
      -Complex.log (1 - (legendreC p : DirichletCharacter ℂ p) q * ((q : ℕ) : ℂ) ^ (-(t : ℂ))) =
        x := by
    intro q
    obtain ⟨c, hc1, hc2, hc⟩ := legendreC_real (p := p) ((q : ℕ) : ZMod p)
    have hq : (1 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.one_lt
    have hqt : ((q : ℕ) : ℝ) ^ (-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    have hqt0 : 0 < ((q : ℕ) : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by linarith) _
    have hpos : 0 < 1 - c * ((q : ℕ) : ℝ) ^ (-t) := by nlinarith
    refine ⟨-Real.log (1 - c * ((q : ℕ) : ℝ) ^ (-t)), ?_⟩
    have hcp : ((q : ℕ) : ℂ) ^ (-(t : ℂ)) = (((q : ℕ) : ℝ) ^ (-t) : ℝ) := by
      rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
    have hc' : (legendreC p : DirichletCharacter ℂ p) q = c := hc
    rw [hc', hcp, show (1 : ℂ) - (c : ℂ) * ((((q : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ) =
      ((1 - c * ((q : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log hpos.le]
    push_cast
    rfl
  choose x hx using hterm
  refine ⟨Real.exp (∑' q : Nat.Primes, x q), Real.exp_pos _, ?_⟩
  rw [hL, Complex.ofReal_exp, Complex.ofReal_tsum]
  exact congrArg Complex.exp (tsum_congr fun q => hx q)

/-- **`L(χ, 1) > 0`**: a nonzero limit of positive reals. -/
theorem LFunction_legendre_one_pos (hp4 : p % 4 = 3) :
    ∃ r : ℝ, 0 < r ∧ ZMod.LFunction (legendreC p : ZMod p → ℂ) 1 = r := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hne := legendreC_ne_one (p := p) hp4
  have hcont : Continuous (DirichletCharacter.LFunction (legendreC p : DirichletCharacter ℂ p)) :=
    (DirichletCharacter.differentiable_LFunction hne).continuous
  have hlim : Tendsto (fun t : ℝ => ZMod.LFunction (legendreC p : ZMod p → ℂ) t)
      (𝓝[>] 1) (𝓝 (ZMod.LFunction (legendreC p : ZMod p → ℂ) 1)) := by
    have := (hcont.comp Complex.continuous_ofReal).tendsto 1
    simp only [Function.comp_def, Complex.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 1, 0 ≤ (ZMod.LFunction (legendreC p : ZMod p → ℂ) t).re ∧
      (ZMod.LFunction (legendreC p : ZMod p → ℂ) t).im = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨r, hr, hre⟩ := LFunction_legendre_real_pos (p := p) ht
    rw [hre]
    exact ⟨by simpa using hr.le, by simp⟩
  have hre : 0 ≤ (ZMod.LFunction (legendreC p : ZMod p → ℂ) 1).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim) (hev.mono fun t ht => ht.1)
  have him : (ZMod.LFunction (legendreC p : ZMod p → ℂ) 1).im = 0 :=
    tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim)
      (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.2.symm))
  have h1 : ZMod.LFunction (legendreC p : ZMod p → ℂ) 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hne
  refine ⟨(ZMod.LFunction (legendreC p : ZMod p → ℂ) 1).re, ?_, ?_⟩
  · rcases hre.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext (by simpa using h.symm) (by simpa using him)) h1
  · exact Complex.ext (by simp) (by simpa using him)

/-! ### Dirichlet's theorem on the excess of residues -/

/-- **Dirichlet.**  For a prime `p ≡ 3 (mod 4)`, the residues below `p/2` outnumber the
non-residues: `Σ_{0<r<p/2} (r/p) > 0`. -/
theorem sum_legendreSym_half_pos (hp4 : p % 4 = 3) :
    0 < ∑ r ∈ range ((p + 1) / 2), legendreSym p r := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨l, hl, hL1⟩ := LFunction_legendre_one_pos (p := p) hp4
  have h0 := LFunction_legendre_zero (p := p) hp4
  rw [LFunction_legendre_zero_eq hp4, hL1] at h0
  -- `T = Σ r χ(r)` is negative
  set T : ℤ := ∑ a ∈ range p, (a : ℤ) * legendreSym p a with hT
  have hTC : ∑ r ∈ range p, (r : ℂ) * legendreSym p r = ((T : ℝ) : ℂ) := by
    rw [hT]; push_cast; rfl
  rw [hTC] at h0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hTneg : (T : ℝ) < 0 := by
    have h0r : Real.sqrt p / Real.pi * l = -(1 / (p : ℝ)) * T := by
      apply Complex.ofReal_injective
      push_cast at h0 ⊢
      exact h0
    have hsp : 0 < Real.sqrt p / Real.pi := div_pos (Real.sqrt_pos.mpr hpR) Real.pi_pos
    have hpos : 0 < Real.sqrt p / Real.pi * l := mul_pos hsp hl
    have : (T : ℝ) = -p * (Real.sqrt p / Real.pi * l) := by
      rw [h0r]; field_simp
    rw [this]; nlinarith
  have hTneg' : T < 0 := by exact_mod_cast hTneg
  have hid := half_sum_identity (p := p) hp4
  rw [← hT] at hid
  have h2 : legendreSym p 2 = 1 ∨ legendreSym p 2 = -1 :=
    legendreSym.eq_one_or_neg_one p (by
      intro h; have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h
      have := Int.le_of_dvd (by norm_num) this
      have := hp.out.two_le; omega)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  rcases h2 with h | h <;> rw [h] at hid <;> nlinarith

end GaloisForLFunctions.RHTower.QuadraticResidueExcess
