import GaloisForLFunctions.AdelicKreinGeometry.TheAdelicProductState
import GaloisForLFunctions.AdelicKreinGeometry.TheWitnessComplementIsPositive
import GaloisForLFunctions.ArithmeticKreinLangerTheory.LocalConstituentsMeetOnlyAtTheIdentity
import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectiveIndexOfTheAtomicKernelIsOneSquare
import GaloisForLFunctions.HTGeometry.RationalTameData

/-!
# The index wall is local

The Hecke states `(nd)^{−s}·1[db ∈ ℤ]` change type at `s = 1/2`: index `0` above, `∞` below
(`negIndex_heckeState`). This file shows that the wall is already present at every single prime.

For a prime `p` the **local Hecke state** (`localHecke`) is

  `φ_{p,s}(x ↦ ax + b) = p^{−s|v_p(a)|} · 1[v_p(b) ≥ min(0, v_p(a))]`,

the condition saying that the image `aℤ_p + b` of `ℤ_p` meets `ℤ_p`. At `s = 1/2` it is the
normalized overlap `vol(B ∩ B')/√(vol B · vol B')` of `p`-adic balls.

* **Local positivity** (`isPosDefKernel_localHecke`): for `s ≥ 1/2` the local state is positive
  definite. Over a common denominator the local Haar state `φ_{p,1/2}` is the commensurability
  kernel of the classes `C_i + p^{v_p(A_i)}ℤ` (`localHecke_half_of_int`), and
  `φ_{p,s} = φ_{p,1/2} · r^{|v_p(a)|}` with `r = p^{−(s−1/2)} ≤ 1` a Poisson kernel on the slope
  valuation (`localHecke_eq_mul`).
* **Local escape** (`localHecke_escape`): translation by `p^{−M}`, `M` large, moves every ball off
  `ℤ_p`, so the local state has index `0` or `∞` at every exponent.
* **Local negativity** (`one_le_negIndex_localHecke`): for `s < 1/2` the dilation by `1/p` against
  the `p` translations by `j/p` gives the form `p − p²·p^{−2s} < 0`.
* **The local wall** (`negIndex_localHecke`): `κ(φ_{p,s}) = 0` for `s ≥ 1/2` and `∞` for `s < 1/2`,
  at every prime.

So the Kakutani threshold is not produced by the infinite product over primes: each prime tower
already carries the full wall, and the global wall is the common value of the local ones.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticKreinLangerTheory (poissonKernel isPosDefKernel_poissonKernel)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic valuation of the slope. -/
def slopeVal : AffineGroupQ →* Multiplicative ℤ := (ratPadicValHom p).comp slopeUnit

theorem toAdd_slopeVal (g : AffineGroupQ) :
    Multiplicative.toAdd (slopeVal p g) = padicValRat p (affSlope g) := rfl

/-- **The local Hecke state** at `p`: `p^{−s|v_p(a)|}` if `aℤ_p + b` meets `ℤ_p`, else `0`. (The
convention `v_p(0) = 0` makes `b = 0` satisfy the condition, as it should.) -/
def localHecke (s : ℝ) (g : AffineGroupQ) : ℂ :=
  if min 0 (padicValRat p (affSlope g)) ≤ padicValRat p (affShift g) then
    (((p : ℝ) ^ (-(s * |(padicValRat p (affSlope g) : ℝ)|)) : ℝ) : ℂ) else 0

theorem isHermKernel_poissonKernel (r : ℝ) : IsHermKernel (poissonKernel r) := fun n => by
  simp [poissonKernel, toAdd_inv, Int.natAbs_neg]

/-- The exponent splits off a Poisson kernel of the slope valuation. -/
theorem localHecke_eq_mul (s : ℝ) (g : AffineGroupQ) :
    localHecke p s g =
      localHecke p (1 / 2) g * poissonKernel ((p : ℝ) ^ (-(s - 1 / 2))) (slopeVal p g) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  simp only [localHecke, poissonKernel, toAdd_slopeVal]
  split_ifs
  · rw [← Complex.ofReal_mul, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0,
      Nat.cast_natAbs, Int.cast_abs]
    congr 2
    ring
  · simp

/-! ### Local positivity -/

/-- **The local Haar state in integer coordinates.** For `a = A'/A`, `b = (C' − C)/A` the local
Haar state is the commensurability kernel of `C + p^{v_p A}ℤ` and `C' + p^{v_p A'}ℤ`. -/
theorem localHecke_half_of_int {g : AffineGroupQ} {A A' C C' : ℤ} (hA : A ≠ 0) (hA' : A' ≠ 0)
    (hsl : affSlope g = (A' : ℚ) / A) (hsh : affShift g = ((C' - C : ℤ) : ℚ) / A) :
    localHecke p (1 / 2) g =
      (commKernel ((p : ℤ) ^ padicValInt p A) C ((p : ℤ) ^ padicValInt p A') C' : ℂ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set k := padicValInt p A
  set k' := padicValInt p A'
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hvs : padicValRat p (affSlope g) = (k' : ℤ) - k := by
    rw [hsl, padicValRat.div (by exact_mod_cast hA') hAq, padicValRat.of_int, padicValRat.of_int]
  -- the gcd of two powers of `p`
  have hgcd : (((p : ℤ) ^ k).gcd ((p : ℤ) ^ k') : ℤ) = (p : ℤ) ^ min k k' := by
    rcases le_total k k' with h | h
    · rw [min_eq_left h, Int.gcd_eq_left (pow_dvd_pow _ h), Int.natAbs_pow, Int.natAbs_ofNat]
      push_cast; rfl
    · rw [min_eq_right h, Int.gcd_comm, Int.gcd_eq_left (pow_dvd_pow _ h), Int.natAbs_pow,
        Int.natAbs_ofNat]
      push_cast; rfl
  -- the support conditions agree
  have hcond : (min 0 (padicValRat p (affSlope g)) ≤ padicValRat p (affShift g)) ↔
      (((p : ℤ) ^ k).gcd ((p : ℤ) ^ k') : ℤ) ∣ C' - C := by
    rw [hgcd, padicValInt_dvd_iff, hvs, hsh]
    by_cases hE : C' - C = 0
    · simp [hE]
    · rw [padicValRat.div (by exact_mod_cast hE) hAq, padicValRat.of_int, padicValRat.of_int]
      simp only [hE, false_or]
      omega
  unfold localHecke commKernel
  by_cases h : min 0 (padicValRat p (affSlope g)) ≤ padicValRat p (affShift g)
  · rw [if_pos h, if_pos (hcond.mp h), hvs]
    have hpk : ∀ j : ℕ, |(((p : ℤ) ^ j : ℤ) : ℝ)| = (p : ℝ) ^ (j : ℝ) := fun j => by
      rw [Real.rpow_natCast]; push_cast; exact abs_of_nonneg (by positivity)
    have hg : ((((p : ℤ) ^ k).gcd ((p : ℤ) ^ k') : ℕ) : ℝ) = (p : ℝ) ^ (min k k' : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hgcd
      push_cast at this
      rw [this, ← Nat.cast_min, Real.rpow_natCast]
    rw [hpk, hpk, hg, ← Real.rpow_add hp0, Real.sqrt_eq_rpow, ← Real.rpow_mul hp0.le,
      ← Real.rpow_sub hp0]
    congr 2
    rcases le_total k k' with hk | hk
    · rw [min_eq_left hk, abs_of_nonneg (by push_cast; exact_mod_cast sub_nonneg.mpr hk)]
      push_cast; ring
    · rw [min_eq_right hk, abs_of_nonpos (by push_cast; exact_mod_cast sub_nonpos.mpr hk)]
      push_cast; ring
  · rw [if_neg h, if_neg (mt hcond.mpr h)]; simp

/-- **The local Haar state is positive definite.** -/
theorem isPosDefOnGroup_localHaar : IsPosDefOnGroup (localHecke p (1 / 2)) := by
  intro N x c
  classical
  set a : Fin N → ℚ := fun i => affSlope (x i) with ha_def
  set b : Fin N → ℚ := fun i => affShift (x i) with hb_def
  set D : ℕ := ∏ i, ((a i).den * (b i).den) with hD_def
  have hD : 0 < D := Finset.prod_pos fun i _ => Nat.mul_pos (a i).den_pos (b i).den_pos
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hint : ∀ q : ℚ, q.den ∣ D → ∃ z : ℤ, (z : ℚ) = D * q := by
    rintro q ⟨t, ht⟩
    refine ⟨t * q.num, ?_⟩
    rw [ht]; push_cast
    rw [mul_comm (q.den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]
  have hdvd_a : ∀ i, (a i).den ∣ D := fun i =>
    (Nat.dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hdvd_b : ∀ i, (b i).den ∣ D := fun i =>
    (Nat.dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  choose A hA using fun i => hint (a i) (hdvd_a i)
  choose C hC using fun i => hint (b i) (hdvd_b i)
  have hA0 : ∀ i, A i ≠ 0 := fun i h => by
    have e := hA i
    rw [h, Int.cast_zero] at e
    rcases mul_eq_zero.mp e.symm with h' | h'
    · exact hDq h'
    · exact affSlope_ne_zero (x i) h'
  have ea : ∀ i, a i = A i / D := fun i => by rw [hA i]; field_simp
  have eb : ∀ i, b i = C i / D := fun i => by rw [hC i]; field_simp
  have key : ∀ i j, localHecke p (1 / 2) ((x i)⁻¹ * x j) =
      (commKernel ((p : ℤ) ^ padicValInt p (A i)) (C i) ((p : ℤ) ^ padicValInt p (A j)) (C j) :
        ℂ) := by
    intro i j
    have hAi : (A i : ℚ) ≠ 0 := by exact_mod_cast hA0 i
    have hsl : affSlope ((x i)⁻¹ * x j) = (A j : ℚ) / A i := by
      rw [affSlope_mul, affSlope_inv]
      change (a i)⁻¹ * a j = _
      rw [ea i, ea j]
      field_simp
    have hsh : affShift ((x i)⁻¹ * x j) = ((C j - C i : ℤ) : ℚ) / A i := by
      rw [affShift_mul, affShift_inv, affSlope_inv]
      change (a i)⁻¹ * b j + -b i / a i = _
      rw [ea i, eb i, eb j]
      push_cast
      field_simp
      ring
    exact localHecke_half_of_int p (hA0 i) (hA0 j) hsl hsh
  have hpA : ∀ i, (p : ℤ) ^ padicValInt p (A i) ≠ 0 := fun i =>
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  obtain ⟨r, hr, h⟩ := commKernel_gram (fun i => (p : ℤ) ^ padicValInt p (A i)) C hpA c
  exact ⟨r, hr, by simp only [key]; exact h⟩

/-- **Local positivity**: for `s ≥ 1/2` the local Hecke state is positive definite. -/
theorem isPosDefKernel_localHecke {s : ℝ} (hs : 1 / 2 ≤ s) : IsPosDefKernel (localHecke p s) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have e : localHecke p s = fun g =>
      localHecke p (1 / 2) g * (poissonKernel ((p : ℝ) ^ (-(s - 1 / 2))) ∘ slopeVal p) g :=
    funext (localHecke_eq_mul p s)
  rw [e]
  exact IsPosDefKernel.mul (isPosDefKernel_iff_isPosDefOnGroup.mpr (isPosDefOnGroup_localHaar p))
    ((isPosDefKernel_poissonKernel (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith))).comp (slopeVal p))

theorem isHermKernel_localHecke (s : ℝ) : IsHermKernel (localHecke p s) := fun g => by
  have h1 := (isPosDefKernel_iff_isPosDefOnGroup.mpr (isPosDefOnGroup_localHaar p)).1 g
  rw [localHecke_eq_mul, localHecke_eq_mul, h1, map_inv, isHermKernel_poissonKernel, map_mul]

/-! ### Local escape -/

/-- **Local escape**: translation by `p^{−M}`, `M` large, moves every ball `g⁻¹(t·h)(ℤ_p)` off
`ℤ_p`. -/
theorem localHecke_escape (s : ℝ) (m n : ℕ) (x : Fin m → AffineGroupQ) (y : Fin n → AffineGroupQ) :
    ∃ t : AffineGroupQ, ∀ a b, localHecke p s ((x a)⁻¹ * (t * y b)) = 0 := by
  classical
  set va : Fin m → ℤ := fun a => padicValRat p (affSlope (x a))
  set vb : Fin n → ℤ := fun b => padicValRat p (affSlope (y b))
  set vd : Fin m → Fin n → ℤ := fun a b => padicValRat p (affShift (y b) - affShift (x a))
  set M : ℕ := 1 + ∑ a, ∑ b, (2 * (va a).natAbs + (vb b).natAbs + (vd a b).natAbs)
  set β : ℚ := ((p : ℚ) ^ M)⁻¹
  refine ⟨translation β, fun a b => ?_⟩
  have hM : ((2 * (va a).natAbs + (vb b).natAbs + (vd a b).natAbs : ℕ) : ℤ) < M := by
    have h1 : 2 * (va a).natAbs + (vb b).natAbs + (vd a b).natAbs ≤
        ∑ b', (2 * (va a).natAbs + (vb b').natAbs + (vd a b').natAbs) :=
      Finset.single_le_sum (f := fun b' => 2 * (va a).natAbs + (vb b').natAbs + (vd a b').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have h2 : ∑ b', (2 * (va a).natAbs + (vb b').natAbs + (vd a b').natAbs) ≤
        ∑ a', ∑ b', (2 * (va a').natAbs + (vb b').natAbs + (vd a' b').natAbs) :=
      Finset.single_le_sum
        (f := fun a' => ∑ b', (2 * (va a').natAbs + (vb b').natAbs + (vd a' b').natAbs))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    exact_mod_cast (show _ < M by omega)
  push_cast at hM
  simp only [Int.natCast_natAbs] at hM
  have hα : affSlope (x a) ≠ 0 := affSlope_ne_zero _
  have hβ0 : β ≠ 0 := inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
  have hβ : padicValRat p β = -(M : ℤ) := padicValRat.self_pow_inv M
  set δ : ℚ := affShift (y b) - affShift (x a)
  -- the shift `δ + β` has valuation `−M`
  have hδβ0 : δ + β ≠ 0 ∧ padicValRat p (δ + β) = -(M : ℤ) := by
    by_cases hδ : δ = 0
    · rw [hδ, zero_add]; exact ⟨hβ0, hβ⟩
    · have hlt : padicValRat p β < padicValRat p δ := by
        rw [hβ]; have := neg_abs_le (vd a b); linarith [abs_nonneg (va a), abs_nonneg (vb b)]
      have hne : β + δ ≠ 0 := fun h => by
        have : δ = -β := by linarith
        rw [this, padicValRat.neg] at hlt; exact lt_irrefl _ hlt
      rw [add_comm]
      exact ⟨hne, (padicValRat.add_eq_of_lt hne hβ0 hδ hlt).trans hβ⟩
  have hsl : affSlope ((x a)⁻¹ * (translation β * y b)) = (affSlope (x a))⁻¹ * affSlope (y b) := by
    rw [affSlope_mul, affSlope_inv, affSlope_mul, affSlope_translation, one_mul]
  have hsh : affShift ((x a)⁻¹ * (translation β * y b)) = (δ + β) / affSlope (x a) := by
    rw [affShift_mul, affShift_inv, affSlope_inv, affShift_mul, affSlope_translation,
      affShift_translation]
    simp only [δ]
    field_simp
    ring
  have hvsl : padicValRat p (affSlope ((x a)⁻¹ * (translation β * y b))) = vb b - va a := by
    rw [hsl, padicValRat.mul (inv_ne_zero hα) (affSlope_ne_zero _), padicValRat.inv]
    simp only [va, vb]; ring
  have hvsh : padicValRat p (affShift ((x a)⁻¹ * (translation β * y b))) = -(M : ℤ) - va a := by
    rw [hsh, padicValRat.div hδβ0.1 hα, hδβ0.2]
  unfold localHecke
  rw [if_neg]
  rw [hvsl, hvsh, not_le]
  have := le_abs_self (va a)
  have := neg_abs_le (va a)
  have := neg_abs_le (vb b)
  exact lt_min (by linarith [abs_nonneg (vd a b)]) (by linarith [abs_nonneg (vd a b)])

/-- Every local Hecke state has index `0` or `∞`. -/
theorem negIndex_localHecke_eq_zero_or_top (s : ℝ) :
    negIndex (localHecke p s) = 0 ∨ negIndex (localHecke p s) = ⊤ :=
  negIndex_eq_zero_or_top_of_escape (isHermKernel_localHecke p s) (localHecke_escape p s)

/-! ### Local negativity -/

/-- **Local negativity**: below `1/2` the dilation by `1/p` and the translations by `j/p`,
`0 ≤ j < p`, with weights `−p^{1−s}` and `1`, have form `p − p²·p^{−2s} < 0`. -/
theorem one_le_negIndex_localHecke {s : ℝ} (hs : s < 1 / 2) : 1 ≤ negIndex (localHecke p s) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hvp : padicValRat p (p : ℚ) = 1 := padicValRat.self hp.out.one_lt
  set u : ℚˣ := Units.mk0 ((p : ℚ)⁻¹) (inv_ne_zero hpq)
  set x : Option (Fin p) → AffineGroupQ :=
    fun o => o.elim (dilation u) fun j => translation ((j : ℚ) / p)
  set y : ℝ := (p : ℝ) ^ (-s)
  set c : Option (Fin p) → ℂ := fun o => o.elim (-((p * y : ℝ) : ℂ)) fun _ => 1
  have h00 : localHecke p s ((x none)⁻¹ * x none) = 1 := by
    simp [localHecke, affSlope_one, affShift_one]
  have h0k : ∀ k : Fin p, localHecke p s ((x none)⁻¹ * x (some k)) = (y : ℂ) := fun k => by
    have hsl : affSlope ((x none)⁻¹ * x (some k)) = p := by
      simp [x, u, affSlope_mul, affSlope_inv, affSlope_dilation, affSlope_translation]
    have hsh : affShift ((x none)⁻¹ * x (some k)) = (k : ℕ) := by
      simp [x, u, affShift_mul, affShift_inv, affSlope_inv, affSlope_dilation, affShift_dilation,
        affShift_translation]
      field_simp
    have hk : (0 : ℤ) ≤ padicValRat p ((k : ℕ) : ℚ) := by
      rw [padicValRat.of_nat]; exact Nat.cast_nonneg _
    simp only [localHecke, hsl, hsh, hvp, y]
    rw [if_pos (by simpa using hk)]
    norm_num
  have hk0 : ∀ k : Fin p, localHecke p s ((x (some k))⁻¹ * x none) = (y : ℂ) := fun k => by
    rw [show (x (some k))⁻¹ * x none = ((x none)⁻¹ * x (some k))⁻¹ by group,
      isHermKernel_localHecke p s, h0k, Complex.conj_ofReal]
  have hjk : ∀ j k : Fin p, localHecke p s ((x (some j))⁻¹ * x (some k)) =
      if j = k then 1 else 0 := fun j k => by
    simp only [x, Option.elim_some, translation_inv_mul]
    by_cases hjk : j = k
    · subst hjk
      simp [localHecke, affSlope_translation, affShift_translation]
    · rw [if_neg hjk]
      have hz : ((k : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
        intro h; exact hjk (Fin.ext (by omega))
      have hnd : ¬ (p : ℤ) ∣ ((k : ℕ) : ℤ) - (j : ℕ) := fun hd => by
        have := Int.eq_zero_of_abs_lt_dvd hd (by
          rw [abs_lt]; constructor <;> push_cast <;> omega)
        exact hz this
      have hv : padicValRat p ((k : ℚ) / p - (j : ℚ) / p) = -1 := by
        rw [← sub_div, show (k : ℚ) - j = ((((k : ℕ) : ℤ) - (j : ℕ) : ℤ) : ℚ) by push_cast; rfl,
          padicValRat.div (by exact_mod_cast hz) hpq, padicValRat.of_int,
          padicValInt.eq_zero_of_not_dvd hnd, hvp]
        rfl
      simp only [localHecke, affSlope_translation, affShift_translation, padicValRat.one, hv]
      rw [if_neg (by norm_num)]
  have hneg : hermQuad (gram (localHecke p s) x) c < 0 := by
    rw [hermQuad_gram]
    have hsum : ∑ a, ∑ b, conj (c a) * localHecke p s ((x a)⁻¹ * x b) * c b =
        ((p - p ^ 2 * (y * y) : ℝ) : ℂ) := by
      simp only [Fintype.sum_option, h00, h0k, hk0, hjk, c, Option.elim_none, Option.elim_some,
        map_neg, Complex.conj_ofReal, map_one, mul_one, one_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [hsum, Complex.ofReal_re]
    -- `p·p^{−2s} > 1`
    have hyy : y * y = (p : ℝ) ^ (-(2 * s)) := by
      rw [← Real.rpow_add hp0]; ring_nf
    have : (1 : ℝ) < p * (p : ℝ) ^ (-(2 * s)) := by
      rw [← Real.rpow_one_add' hp0.le (by linarith)]
      exact Real.one_lt_rpow hp1 (by linarith)
    rw [hyy]; nlinarith
  have h1 := one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg
  exact le_trans (by exact_mod_cast h1.trans (negIndexOn_le_hermNegIndex _ ⊤))
    (hermNegIndex_gram_le_negIndex (localHecke p s) _)

/-- **The local wall**: at every prime, `κ(φ_{p,s}) = 0` for `s ≥ 1/2` and `∞` for `s < 1/2`. -/
theorem negIndex_localHecke (s : ℝ) :
    negIndex (localHecke p s) = if 1 / 2 ≤ s then 0 else ⊤ := by
  split_ifs with hs
  · exact (isPosDefKernel_localHecke p hs).negIndex_eq_zero
  · rcases negIndex_localHecke_eq_zero_or_top p s with h | h
    · have := one_le_negIndex_localHecke p (not_le.mp hs)
      rw [h] at this
      exact absurd this (by norm_num)
    · exact h

end GaloisForLFunctions.AdelicKreinGeometry
