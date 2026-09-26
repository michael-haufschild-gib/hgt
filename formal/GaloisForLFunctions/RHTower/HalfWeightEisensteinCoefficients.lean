import GaloisForLFunctions.RHTower.HalfWeightEisensteinFourier
import GaloisForLFunctions.RHTower.CoprimeClassExact

/-!
# Fourier coefficients of the weight-½ Eisenstein series as Dirichlet series

* `Ccoef_eq_gauss`: `C(c,d) = G(-d;c)(ic)^{1/2}/(√2 c)` (from `|G(-d;c)|² = 2c`); hence
  `norm_Ccoef`: `|C(c,d)| = 1`, and `norm_klH_le`: `|klH(n,c)| ≤ c`.
* `klH_pos_eq`: `klH(n,c) = (ic)^{1/2}/(√2 c) Σ_{m mod c} g_ψ(n - m²; c)` with the twisted Ramanujan
  sum `g_ψ(k;c) = Σ_{(r,c)=1} ψ̄(r) e(rk/c)`.
* `ramSum_eq`, `sum_ramSum_sq`: for the trivial character `g = c_c` (Ramanujan sum,
  `c_c(k) = Σ_{e|c} μ(e)(c/e)[(c/e)|k]`) and
  `Σ_{m mod c} c_c(n - m²) = c Σ_{e|c} μ(e) N_{c/e}(n)` with `N_f(n) = #{m mod f : m² ≡ n}`.
* `rowR_neg`, `eisHalf_eq_pos_rows`: `row_{-c} = ψ̄(-1) row_c`, so
  `E = (1 + ψ̄(-1))(y^w + Σ_{c≥1} row_c)`.
* `eisHalf_eq_coeffs` (`Re w > 1`): `E(z,w;ψ) = (1 + ψ̄(-1))(y^w + Σ_n 𝓕kerH_{y,w}(n) e(nx) D_n(w))`,
  `D_n(w) = Σ_{c≥1, 4M|c} c^{-2w} klH(n,c)` (absolute convergence over `ℕ × ℤ`).
* `Dser_one`: for the trivial nebentypus
  `D_n(w) = i^{1/2}/√2 · Σ_{c≥1, 4M|c} c^{1/2-2w} (μ * N(n))(c)`.

The analytic continuation of `D_n` reduces to the Euler product of `Σ_{4M|c} (μ*N(n))(c) c^{-s}`,
`s = 2w - 1/2`: local factors `1 + (n/p) p^{-s}` for `p ∤ 2Mn`, i.e. `L(s, χ_n)/ζ(2s)` up to finitely
many finite local sums.
-/

open Complex Matrix CongruenceSubgroup
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

/-! ### The unimodular coefficient through the Gauss sum -/

theorem mul_star_eq_norm_sq (a : ℂ) : a * starRingEnd ℂ a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `C(c,d) = G(-d;c) (ic)^{1/2} / (√2 c)` for `4 ∣ c`, `(c,d) = 1`. -/
theorem Ccoef_eq_gauss {c : ℕ} [NeZero c] (h4 : (4 : ℤ) ∣ c) {d : ℤ} (hcd : IsCoprime (c : ℤ) d) :
    Ccoef c d = gaussQ (-d) c * (I * c) ^ (1 / 2 : ℂ) / (Real.sqrt 2 * c) := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne c))
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  have hG := norm_sq_gaussQ h4 hcd
  have hG0 : gaussQ (-d) c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hG; norm_num at hG; exact (NeZero.ne c) (by exact_mod_cast hG)
  set P := (I * c) ^ (1 / 2 : ℂ) with hP
  have hPn : ‖P‖ ^ 2 = c := by
    rw [hP, norm_cpow_half, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hP0 : P ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hPn; norm_num at hPn; exact (NeZero.ne c) (by exact_mod_cast hPn.symm)
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  have e1 := mul_star_eq_norm_sq (gaussQ (-d) c)
  have e2 := mul_star_eq_norm_sq P
  rw [hG] at e1
  rw [hPn] at e2
  have hG0' : starRingEnd ℂ (gaussQ (-d) c) ≠ 0 := by rwa [map_ne_zero]
  have hP0' : starRingEnd ℂ P ≠ 0 := by rwa [map_ne_zero]
  unfold Ccoef
  rw [← hP, div_eq_div_iff (mul_ne_zero hG0' hP0') (mul_ne_zero hs2 hc)]
  have hsq : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  push_cast at e1 e2
  linear_combination (c : ℂ) ^ 2 * hsq - (P * starRingEnd ℂ P) * e1 - (2 * (c : ℂ)) * e2

/-! ### `klH` through character-twisted Ramanujan sums -/

variable (M : ℕ) (ψ : DirichletCharacter ℂ (4 * M))

/-- The twisted Ramanujan sum `g_ψ(k; c) = Σ_{r mod c, (c,r)=1} ψ̄(r) e(rk/c)`. -/
noncomputable def gPsi (k : ℤ) (c : ℕ) : ℂ :=
  ∑ r ∈ Finset.range c, if IsCoprime (c : ℤ) (r : ℤ) then
    starRingEnd ℂ (ψ ((r : ℤ) : ZMod (4 * M))) * cexp (2 * π * I * k * (r : ℂ) / c) else 0

/-- For `c > 0` with `4 ∣ c`: `klH(n, c) = (ic)^{1/2}/(√2 c) · Σ_{m mod c} g_ψ(n - m²; c)`. -/
theorem klH_pos_eq {c : ℕ} [NeZero c] (h4 : (4 : ℤ) ∣ c) (n : ℤ) :
    klH M ψ n c = (I * c) ^ (1 / 2 : ℂ) / (Real.sqrt 2 * c) *
      ∑ m ∈ Finset.range c, gPsi M ψ (n - (m : ℤ) ^ 2) c := by
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  have hcpos : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  unfold klH gPsi
  rw [Int.natAbs_natCast, Int.sign_eq_one_of_pos hcpos]
  simp only [one_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hcop : IsCoprime (c : ℤ) (r : ℤ)
  · simp only [if_pos hcop]
    rw [Ccoef_eq_gauss h4 hcop, gaussQ,
      Fin.sum_univ_eq_sum_range (fun m => cexp (2 * π * I * (((-(r : ℤ)) : ℤ) * ((m : ℕ) : ℂ) ^ 2 / c)))]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show 2 * π * I * ((n - (m : ℤ) ^ 2 : ℤ) : ℂ) * (r : ℂ) / c =
        2 * π * I * (((-(r : ℤ)) : ℤ) * ((m : ℕ) : ℂ) ^ 2 / c) + 2 * π * I * n * (r : ℂ) / c by
        push_cast; ring, Complex.exp_add]
    push_cast
    ring
  · simp only [if_neg hcop, Finset.sum_const_zero, mul_zero]

/-! ### Ramanujan sums over squares -/

open GaloisForLFunctions.RHTower.CoprimeClassCount GaloisForLFunctions.RHTower.CoprimeClassExact
  GaloisForLFunctions.RHTower.CoprimeClassRamanujan ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The Ramanujan sum `c_c(k) = Σ_{r < c, (r,c) = 1} e(kr/c)`. -/
noncomputable def ramSum (k : ℤ) (c : ℕ) : ℂ :=
  ∑ r ∈ Finset.range c, if c.Coprime r then ph k c r else 0

/-- `N_f(n) = #{m mod f : m² ≡ n (mod f)}`, as a complex number. -/
noncomputable def sqCount (n : ℤ) (f : ℕ) : ℂ :=
  ∑ m ∈ Finset.range f, if (f : ℤ) ∣ n - (m : ℤ) ^ 2 then 1 else 0

theorem sum_range_dvd {c e : ℕ} (he : 0 < e) (hec : e ∣ c) (g : ℕ → ℂ) :
    ∑ r ∈ Finset.range c, (if e ∣ r then g r else 0) = ∑ s ∈ Finset.range (c / e), g (e * s) := by
  rw [← Finset.sum_filter]
  have himg : (Finset.range c).filter (e ∣ ·) = (Finset.range (c / e)).image (e * ·) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hr, s, rfl⟩
      refine ⟨s, ?_, rfl⟩
      obtain ⟨t, rfl⟩ := hec
      rw [Nat.mul_div_cancel_left _ he]
      exact (Nat.mul_lt_mul_left he).1 hr
    · rintro ⟨s, hs, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      obtain ⟨t, rfl⟩ := hec
      rw [Nat.mul_div_cancel_left _ he] at hs
      exact (Nat.mul_lt_mul_left he).2 hs
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left he h)]

/-- **Möbius evaluation of the Ramanujan sum**: `c_c(k) = Σ_{e ∣ c} μ(e) (c/e) [(c/e) ∣ k]`. -/
theorem ramSum_eq {c : ℕ} (hc : 0 < c) (k : ℤ) :
    ramSum k c = ∑ e ∈ c.divisors, (μ e : ℂ) *
      (if ((c / e : ℕ) : ℤ) ∣ k then ((c / e : ℕ) : ℂ) else 0) := by
  unfold ramSum
  have h1 : ∀ r ∈ Finset.range c, (if c.Coprime r then ph k c r else 0) =
      ∑ e ∈ c.divisors, (μ e : ℂ) * (if e ∣ r then ph k c r else 0) := by
    intro r _
    have hci := coprime_indicator hc r
    have hci' : (if c.Coprime r then (1 : ℂ) else 0) =
        ∑ e ∈ c.divisors, if e ∣ r then (μ e : ℂ) else 0 := by
      have := congrArg (fun t : ℤ => (t : ℂ)) hci
      push_cast at this
      exact this
    calc (if c.Coprime r then ph k c r else 0)
        = (if c.Coprime r then (1 : ℂ) else 0) * ph k c r := by split_ifs <;> simp
      _ = _ := by
        rw [hci', Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  have hec : e ∣ c := Nat.dvd_of_mem_divisors he
  rw [← Finset.mul_sum, sum_range_dvd he0 hec]
  have hce : 0 < c / e := Nat.div_pos (Nat.le_of_dvd hc hec) he0
  have hph : ∀ s, ph k c (e * s) = ph k (c / e) s := by
    intro s
    unfold ph
    congr 1
    have hc' : ((c / e : ℕ) : ℂ) = (c : ℂ) / e := by
      rw [Nat.cast_div hec (by exact_mod_cast he0.ne')]
    have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [hc']
    push_cast
    field_simp
  simp_rw [hph]
  rw [geom_eq hce]

theorem sum_range_mul_mod (q f : ℕ) (g : ℕ → ℂ) :
    ∑ m ∈ Finset.range (q * f), g (m % f) = q * ∑ r ∈ Finset.range f, g r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih]
    have : ∀ x ∈ Finset.range f, g ((q * f + x) % f) = g x := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [Nat.mul_add_mod_of_lt hx]
    rw [Finset.sum_congr rfl this]
    push_cast; ring

theorem dvd_sub_sq_mod_iff {f : ℕ} (n : ℤ) (m : ℕ) :
    (f : ℤ) ∣ n - (m : ℤ) ^ 2 ↔ (f : ℤ) ∣ n - ((m % f : ℕ) : ℤ) ^ 2 := by
  have h : ((m % f : ℕ) : ℤ) ≡ (m : ℤ) [ZMOD f] := by
    rw [Int.natCast_mod]; exact Int.mod_modEq _ _
  have h2 : ((m % f : ℕ) : ℤ) ^ 2 ≡ (m : ℤ) ^ 2 [ZMOD f] := h.pow 2
  have key : n - (m : ℤ) ^ 2 ≡ n - ((m % f : ℕ) : ℤ) ^ 2 [ZMOD f] := Int.ModEq.sub_left n h2.symm
  rw [← Int.modEq_zero_iff_dvd, ← Int.modEq_zero_iff_dvd]
  exact ⟨fun h => key.symm.trans h, fun h => key.trans h⟩

/-- `#{m < c : f ∣ n - m²} = (c/f) N_f(n)` for `f ∣ c`. -/
theorem sum_dvd_sub_sq {c f : ℕ} (hfc : f ∣ c) (n : ℤ) :
    ∑ m ∈ Finset.range c, (if (f : ℤ) ∣ n - (m : ℤ) ^ 2 then (1 : ℂ) else 0) =
      (c / f : ℕ) * sqCount n f := by
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf
    obtain ⟨t, rfl⟩ := hfc
    simp [sqCount]
  obtain ⟨q, rfl⟩ := hfc
  rw [Nat.mul_div_cancel_left _ hf, mul_comm f q]
  have h := sum_range_mul_mod q f (fun r => if (f : ℤ) ∣ n - (r : ℤ) ^ 2 then (1 : ℂ) else 0)
  rw [sqCount, ← h]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [← dvd_sub_sq_mod_iff (f := f) n m]

/-- **Ramanujan sums over squares**: `Σ_{m mod c} c_c(n - m²) = c Σ_{e ∣ c} μ(e) N_{c/e}(n)`. -/
theorem sum_ramSum_sq {c : ℕ} (hc : 0 < c) (n : ℤ) :
    ∑ m ∈ Finset.range c, ramSum (n - (m : ℤ) ^ 2) c =
      c * ∑ e ∈ c.divisors, (μ e : ℂ) * sqCount n (c / e) := by
  simp_rw [ramSum_eq hc]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  have hec : e ∣ c := Nat.dvd_of_mem_divisors he
  have hf : (c / e) ∣ c := Nat.div_dvd_of_dvd hec
  rw [← Finset.mul_sum]
  have h1 : ∀ m ∈ Finset.range c, (if ((c / e : ℕ) : ℤ) ∣ n - (m : ℤ) ^ 2 then ((c / e : ℕ) : ℂ) else 0) =
      ((c / e : ℕ) : ℂ) * (if ((c / e : ℕ) : ℤ) ∣ n - (m : ℤ) ^ 2 then (1 : ℂ) else 0) := by
    intro m _; split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_dvd_sub_sq hf n,
    Nat.div_div_self hec hc.ne']
  have hce : ((c / e : ℕ) : ℂ) * (e : ℂ) = c := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hec]
  rw [← hce]; ring

/-! ### The trivial nebentypus -/

/-- For the trivial character and `4M ∣ c`, `g_ψ` is the Ramanujan sum. -/
theorem gPsi_one {c : ℕ} (h4 : 4 * M ∣ c) (k : ℤ) :
    gPsi M (1 : DirichletCharacter ℂ (4 * M)) k c = ramSum k c := by
  unfold gPsi ramSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hiff : IsCoprime (c : ℤ) (r : ℤ) ↔ c.Coprime r := Nat.isCoprime_iff_coprime
  by_cases hcop : c.Coprime r
  · rw [if_pos (hiff.2 hcop), if_pos hcop]
    have hunit : IsUnit ((r : ℤ) : ZMod (4 * M)) := by
      have : IsUnit ((r : ℕ) : ZMod (4 * M)) :=
        (ZMod.isUnit_iff_coprime r (4 * M)).2 (Nat.Coprime.coprime_dvd_right h4 hcop.symm)
      simpa using this
    rw [MulChar.one_apply hunit, map_one, one_mul]
    unfold ph
    ring_nf
  · rw [if_neg (fun h => hcop (hiff.1 h)), if_neg hcop]

/-- `Σ_{e ∣ c} μ(e) N_{c/e}(n)`: the Dirichlet convolution `μ * N(n)` at `c`. -/
noncomputable def muN (n : ℤ) (c : ℕ) : ℂ := ∑ e ∈ c.divisors, (μ e : ℂ) * sqCount n (c / e)

/-- **The coefficient sum for the trivial nebentypus**: for `c > 0`, `4M ∣ c`,
`klH(n, c) = (ic)^{1/2}/√2 · Σ_{e ∣ c} μ(e) N_{c/e}(n)`. -/
theorem klH_one_pos {c : ℕ} [NeZero c] (h4 : 4 * M ∣ c) (n : ℤ) :
    klH M (1 : DirichletCharacter ℂ (4 * M)) n c =
      (I * c) ^ (1 / 2 : ℂ) / Real.sqrt 2 * muN n c := by
  have h4' : (4 : ℤ) ∣ c := by
    have : (4 : ℕ) ∣ c := dvd_trans (dvd_mul_right 4 M) h4
    exact_mod_cast this
  have hc : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  rw [klH_pos_eq M _ h4' n]
  simp_rw [gPsi_one M h4]
  rw [sum_ramSum_sq hc n, muN]
  field_simp

/-! ### Symmetry `c ↦ -c` and the positive rows -/

theorem mem_adm4_neg_iff (c d : ℤ) : (-c, -d) ∈ adm4 M ↔ (c, d) ∈ adm4 M := by
  simp only [adm4, Set.mem_setOf_eq, dvd_neg, IsCoprime.neg_neg_iff]

theorem Fp_neg (w : ℂ) (z : UpperHalfPlane) (c d : ℤ) :
    Fp M ψ w z (-c, -d) = starRingEnd ℂ (ψ (-1)) * Fp M ψ w z (c, d) := by
  unfold Fp
  have hψ : ψ ((-d : ℤ) : ZMod (4 * M)) = ψ (-1) * ψ ((d : ℤ) : ZMod (4 * M)) := by
    rw [← map_mul]; push_cast; ring_nf
  simp only [neg_eq_zero, Int.natAbs_neg, Int.sign_neg]
  rw [hψ, map_mul]
  by_cases hc : c = 0
  · simp only [hc, if_true]; ring
  · simp only [hc, if_false]
    have h1 : -c.sign * -d = c.sign * d := by ring
    have h2 : ((-d : ℤ) : ℝ) / ((-c : ℤ) : ℝ) = (d : ℝ) / c := by push_cast; rw [neg_div_neg_eq]
    rw [h1, h2]
    ring

theorem rowR_neg (w : ℂ) (z : UpperHalfPlane) (c : ℤ) :
    rowR M ψ w z (-c) = starRingEnd ℂ (ψ (-1)) * rowR M ψ w z c := by
  unfold rowR
  rw [← (Equiv.neg ℤ).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun d => ?_
  simp only [Equiv.neg_apply]
  by_cases h : (c, d) ∈ adm4 M
  · rw [Set.indicator_of_mem ((mem_adm4_neg_iff M c d).2 h), Set.indicator_of_mem h, Fp_neg]
  · rw [Set.indicator_of_notMem (fun h' => h ((mem_adm4_neg_iff M c d).1 h')),
      Set.indicator_of_notMem h, mul_zero]

/-- `E = (1 + ψ̄(-1)) (y^w + Σ_{c ≥ 1} row_c)` for `Re w > 1`. -/
theorem eisHalf_eq_pos_rows {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisHalf M ψ w z = (1 + starRingEnd ℂ (ψ (-1))) *
      (((z.im : ℝ) : ℂ) ^ w + ∑' k : ℕ, rowR M ψ w z ((k : ℤ) + 1)) := by
  rw [eisHalf_eq_tsum_rows M ψ hw z]
  have hs := (summable_indicator M ψ hw z).of_norm
  have hrow : Summable (rowR M ψ w z) := hs.prod
  have h1 : Summable fun k : ℕ => rowR M ψ w z ((k : ℤ) + 1) :=
    hrow.comp_injective (fun a b h => by simpa using h)
  have h2 : Summable fun k : ℕ => rowR M ψ w z (-((k : ℤ) + 1)) :=
    hrow.comp_injective (fun a b h => by simpa using h)
  rw [tsum_of_add_one_of_neg_add_one h1 h2, rowR_zero]
  simp_rw [rowR_neg]
  rw [tsum_mul_left]
  ring

/-! ### Bounds and the exchange of summations -/

theorem norm_Ccoef {c : ℕ} [NeZero c] (h4 : (4 : ℤ) ∣ c) {d : ℤ} (hcd : IsCoprime (c : ℤ) d) :
    ‖Ccoef c d‖ = 1 := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne c))
  rw [Ccoef_eq_gauss h4 hcd, norm_div, norm_mul, norm_mul, norm_cpow_half]
  have hG := norm_sq_gaussQ h4 hcd
  have hG' : ‖gaussQ (-d) c‖ = Real.sqrt 2 * Real.sqrt c := by
    rw [← Real.sqrt_mul (by norm_num), ← hG, Real.sqrt_sq (norm_nonneg _)]
  rw [hG']
  have hIc : ‖I * (c : ℂ)‖ = c := by simp
  rw [hIc, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), ← Real.sqrt_eq_rpow]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hcR
  have : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hcR.le
  field_simp
  nlinarith [this]

theorem norm_klH_le {c : ℕ} [NeZero c] (h4 : (4 : ℤ) ∣ c) (n : ℤ) :
    ‖klH M ψ n c‖ ≤ c := by
  unfold klH
  rw [Int.natAbs_natCast]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ r ∈ Finset.range c, ‖(if IsCoprime (c : ℤ) (r : ℤ) then
      starRingEnd ℂ (ψ ((r : ℤ) : ZMod (4 * M))) * Ccoef c ((c : ℤ).sign * r) *
        cexp (2 * π * I * n * (r : ℂ) / ((c : ℤ) : ℂ)) else 0)‖ ≤ 1 := by
    intro r _
    split_ifs with hcop
    · have hpos : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
      rw [Int.sign_eq_one_of_pos hpos, one_mul, norm_mul, norm_mul, Complex.norm_conj,
        norm_Ccoef h4 hcop, mul_one]
      have h1 := norm_char_le M ψ ((r : ℤ) : ZMod (4 * M))
      have h2 : ‖cexp (2 * π * I * n * (r : ℂ) / ((c : ℤ) : ℂ))‖ = 1 := by
        rw [show (2 * π * I * n * (r : ℂ) / ((c : ℤ) : ℂ)) =
          2 * π * I * (((n : ℝ) * r / c : ℝ) : ℂ) by push_cast; ring]
        exact norm_cexp_two_pi_I_mul _
      rw [h2, mul_one]; exact h1
    · simp
  calc ∑ r ∈ Finset.range c, _ ≤ ∑ r ∈ Finset.range c, (1 : ℝ) := Finset.sum_le_sum hb
    _ = c := by simp

/-- The Dirichlet series of the `n`-th Fourier coefficient:
`D_n(w) = Σ_{c ≥ 1, 4M ∣ c} c^{-2w} klH(n, c)`. -/
noncomputable def Dser (n : ℤ) (w : ℂ) : ℂ :=
  ∑' k : ℕ, if 4 * M ∣ k + 1 then ((k + 1 : ℕ) : ℂ) ^ (-2 * w) * klH M ψ n ((k + 1 : ℕ) : ℤ) else 0

theorem norm_natCast_cpow (k : ℕ) (w : ℂ) :
    ‖((k + 1 : ℕ) : ℂ) ^ (-2 * w)‖ = ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k)]
  congr 1; simp

theorem summable_shift_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * σ) := by
  have h := Real.summable_nat_rpow.2 (show 1 - 2 * σ < -1 by linarith)
  exact (summable_nat_add_iff 1).2 h |>.congr fun k => by push_cast; rfl

/-- **The coefficient form of the Fourier expansion** (`Re w > 1`):
`E(z,w;ψ) = (1 + ψ̄(-1)) (y^w + Σ_n 𝓕kerH_{y,w}(n) e(nx) D_n(w))`. -/
theorem eisHalf_eq_coeffs {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisHalf M ψ w z = (1 + starRingEnd ℂ (ψ (-1))) *
      (((z.im : ℝ) : ℂ) ^ w + ∑' n : ℤ, FourierTransform.fourier (kerH z.im w) n *
        cexp (2 * π * I * n * z.re) * Dser M ψ n w) := by
  rw [eisHalf_eq_pos_rows M ψ hw z]
  congr 2
  set T : ℕ → ℤ → ℂ := fun k n => if 4 * M ∣ k + 1 then ((k + 1 : ℕ) : ℂ) ^ (-2 * w) *
    (FourierTransform.fourier (kerH z.im w) n * cexp (2 * π * I * n * z.re) *
      klH M ψ n ((k + 1 : ℕ) : ℤ)) else 0 with hT
  have hrow : ∀ k : ℕ, rowR M ψ w z ((k : ℤ) + 1) = ∑' n : ℤ, T k n := by
    intro k
    have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    by_cases h4 : 4 * M ∣ k + 1
    · have h4' : (4 * M : ℤ) ∣ ((k : ℤ) + 1) := by rw [hk]; exact_mod_cast h4
      rw [rowR_ne_zero M ψ hw z (by omega) h4', hk, Int.natAbs_natCast, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      simp only [hT, if_pos h4]
    · have h4' : ¬ (4 * M : ℤ) ∣ ((k : ℤ) + 1) := by rw [hk]; exact_mod_cast h4
      rw [rowR_of_not_dvd M ψ w z h4']
      simp only [hT, if_neg h4, tsum_zero]
  simp_rw [hrow]
  -- absolute summability over `ℕ × ℤ`
  have hF := summable_norm_fourier_kerH z.im_pos (show 1 / 2 < w.re by linarith)
  have hA := summable_shift_rpow hw
  have hbound : ∀ k n, ‖T k n‖ ≤ ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * w.re) *
      ‖FourierTransform.fourier (kerH z.im w) n‖ := by
    intro k n
    simp only [hT]
    split_ifs with h4
    · haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
      have h4' : (4 : ℤ) ∣ ((k + 1 : ℕ) : ℤ) := by
        have : (4 : ℕ) ∣ k + 1 := dvd_trans (dvd_mul_right 4 M) h4
        exact_mod_cast this
      rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow]
      have he : ‖cexp (2 * π * I * n * z.re)‖ = 1 := by
        rw [show (2 * π * I * n * z.re : ℂ) = 2 * π * I * (((n : ℝ) * z.re : ℝ) : ℂ) by
          push_cast; ring]
        exact norm_cexp_two_pi_I_mul _
      rw [he, mul_one]
      have hk := norm_klH_le M ψ h4' n
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hpow : ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * w.re) =
          ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) * ((k + 1 : ℕ) : ℝ) := by
        rw [show (1 - 2 * w.re) = -2 * w.re + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
      rw [hpow]
      have h0 : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) := by positivity
      calc ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) * (‖FourierTransform.fourier (kerH z.im w) n‖ *
            ‖klH M ψ n ((k + 1 : ℕ) : ℤ)‖)
          ≤ ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) * (‖FourierTransform.fourier (kerH z.im w) n‖ *
            ((k + 1 : ℕ) : ℝ)) := by gcongr
        _ = _ := by ring
    · simp only [norm_zero]; positivity
  have hprod : Summable fun p : ℕ × ℤ => ((p.1 + 1 : ℕ) : ℝ) ^ (1 - 2 * w.re) *
      ‖FourierTransform.fourier (kerH z.im w) p.2‖ :=
    hA.mul_of_nonneg hF (fun k => by positivity) (fun n => norm_nonneg _)
  have hTs : Summable (Function.uncurry T) :=
    Summable.of_norm_bounded hprod (fun p => hbound p.1 p.2)
  rw [← hTs.tsum_comm' (fun k => hTs.prod_factor k)
    (fun n => (hTs.comp_injective (fun a b h => by simpa using h) :
      Summable fun k => Function.uncurry T (k, n)))]
  refine tsum_congr fun n => ?_
  unfold Dser
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [hT]
  split_ifs <;> ring

/-- **The coefficient series for the trivial nebentypus**:
`D_n(w) = i^{1/2}/√2 · Σ_{c ≥ 1, 4M ∣ c} c^{1/2 - 2w} Σ_{e ∣ c} μ(e) N_{c/e}(n)`. -/
theorem Dser_one (n : ℤ) (w : ℂ) :
    Dser M (1 : DirichletCharacter ℂ (4 * M)) n w = I ^ (1 / 2 : ℂ) / Real.sqrt 2 *
      ∑' k : ℕ, if 4 * M ∣ k + 1 then ((k + 1 : ℕ) : ℂ) ^ (1 / 2 - 2 * w) * muN n (k + 1)
        else 0 := by
  unfold Dser
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  split_ifs with h4
  · haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
    rw [Int.natCast_add, Int.natCast_one]
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, klH_one_pos M h4 n]
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsplit : (I * ((k + 1 : ℕ) : ℂ)) ^ (1 / 2 : ℂ) =
        I ^ (1 / 2 : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ) := by
      have := cpow_mul_ofReal_pos (x := I) Complex.I_ne_zero hpos (1 / 2 : ℂ)
      simpa using this
    have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [hsplit, show (1 / 2 - 2 * w : ℂ) = -2 * w + 1 / 2 by ring, Complex.cpow_add _ _ hk0]
    ring
  · simp

end GaloisForLFunctions.RHTower.HalfWeight
