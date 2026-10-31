import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap

/-!
# Conformal symmetry needs a negative square

Over `𝔽_q` Frobenius acts on the intersection form of `C × C` with conformal factor `q`. Over `ℤ`
the Hecke dilations act on the scaling surface as isometric boosts, never conformally
(`ArithmeticLorentzianGeometry.FrobeniusIsConformalHeckeIsABoost`). This file locates the
conformal symmetries of states.

* **Positive states have none** (`eq_zero_of_conformal_of_isPosDefKernel`). An endomorphism `α` of
  a group fixes the identity; `φ ∘ α = λφ` with `λ ≠ 1` forces `φ(1) = 0`, and a positive-definite
  kernel is bounded by `φ(1)`. In particular no nonzero positive state on `Aff(ℚ)` has a successor
  on which a dilation acts conformally with factor `≠ 1` (`eq_zero_of_conformal_successor`).
* **Conformal successors are homogeneous** (`conformal_successor_eq`): a function on `ℚ` with
  `φ(ub) = |u|^s φ(b)`, `s ≠ 0`, is `|b|^s φ(1)`.
* **Exponent one** (`negIndex_mul_absRat`). The conformal successors `c|b|` with factor `|u|` have
  index `0` for `c = 0`, exactly `1` for `c < 0`, and `∞` for `c > 0`. The kernel `−|b|` is
  conditionally positive (`polarIndex_negAbsRat`), and strictly so on distinct points; `|b|` is
  then negative definite on the whole polar hyperplane of any family of distinct points
  (`hermQuad_gram_absRat_neg`).

So a conformal symmetry with factor `≠ 1` exists only on indefinite states, and among the
successors of exponent one the finite-index ones are exactly the index-one states `−c|b|`,
`c > 0`. The conformal factor of the dilation `x ↦ ux` is the archimedean size `|u|`: over `ℤ`
the conformal part of Frobenius lives on the additive side, carried by one negative square, while
the multiplicative side carries the boost.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Positive states admit no conformal symmetry -/

/-- **Positive states admit no conformal symmetry.** If `φ ∘ α = c·φ` for an endomorphism `α` and
`c ≠ 1`, a positive-definite kernel vanishes. -/
theorem eq_zero_of_conformal_of_isPosDefKernel {G : Type*} [Group G] {φ : G → ℂ}
    (hφ : IsPosDefKernel φ) (α : G →* G) {c : ℂ} (hc : c ≠ 1) (hconf : ∀ g, φ (α g) = c * φ g)
    (g : G) : φ g = 0 := by
  have h1 : φ 1 = 0 := by
    have h := hconf 1
    rw [map_one] at h
    have h' : (1 - c) * φ 1 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have := hφ.norm_le g
  rw [h1, Complex.zero_re] at this
  exact norm_le_zero_iff.mp this

/-- The dilation `b ↦ ub` of the translation group of `ℚ`. -/
def ratDilation (u : ℚ) : Multiplicative ℚ →* Multiplicative ℚ where
  toFun b := Multiplicative.ofAdd (u * Multiplicative.toAdd b)
  map_one' := by simp
  map_mul' a b := by simp [mul_add]

/-- **No positive successor is conformal.** A positive-definite function on the translations of `ℚ`
on which some dilation acts with factor `c ≠ 1` vanishes. -/
theorem eq_zero_of_conformal_successor {ψ : Multiplicative ℚ → ℂ} (hψ : IsPosDefKernel ψ)
    (u : ℚ) {c : ℂ} (hc : c ≠ 1) (hconf : ∀ b, ψ (ratDilation u b) = c * ψ b) (b : Multiplicative ℚ) :
    ψ b = 0 :=
  eq_zero_of_conformal_of_isPosDefKernel hψ (ratDilation u) hc hconf b

/-- **Conformal successors are homogeneous.** -/
theorem conformal_successor_eq {φ : Multiplicative ℚ → ℂ} {s : ℝ} (hs : s ≠ 0)
    (hconf : ∀ u b : ℚ, u ≠ 0 →
      φ (Multiplicative.ofAdd (u * b)) = (((|u| : ℝ) ^ s : ℝ) : ℂ) * φ (Multiplicative.ofAdd b))
    (b : ℚ) : φ (Multiplicative.ofAdd b) = (((|b| : ℝ) ^ s : ℝ) : ℂ) * φ (Multiplicative.ofAdd 1) := by
  rcases eq_or_ne b 0 with rfl | hb
  · have h := hconf 2 0 two_ne_zero
    rw [mul_zero] at h
    have h2 : (|((2 : ℚ) : ℝ)|) ^ s ≠ 1 := by
      rw [Rat.cast_ofNat, abs_two]
      intro h1
      have hl := congrArg Real.log h1
      rw [Real.log_rpow (by norm_num), Real.log_one] at hl
      exact hs ((mul_eq_zero.mp hl).resolve_right (Real.log_pos (by norm_num)).ne')
    have h0 : φ (Multiplicative.ofAdd 0) = 0 := by
      have h' : (1 - (((|(2 : ℚ)| : ℝ) ^ s : ℝ) : ℂ)) * φ (Multiplicative.ofAdd 0) = 0 := by
        linear_combination h
      refine (mul_eq_zero.mp h').resolve_left fun h1 => h2 ?_
      exact_mod_cast (sub_eq_zero.mp h1).symm
    rw [h0]
    simp [Real.zero_rpow hs]
  · simpa using hconf b 1 hb

/-! ### The kernels `±|b|` on `ℚ` -/

/-- The kernel `b ↦ |b|` on the translations of `ℚ`. -/
def absRat (m : Multiplicative ℚ) : ℂ := ((|Multiplicative.toAdd m| : ℚ) : ℂ)

/-- The kernel `b ↦ −|b|`. -/
def negAbsRat (m : Multiplicative ℚ) : ℂ := -absRat m

theorem absRat_conformal (u : ℚ) (b : Multiplicative ℚ) :
    absRat (ratDilation u b) = ((|u| : ℚ) : ℂ) * absRat b := by
  simp [absRat, ratDilation, abs_mul]

theorem isHermKernel_absRat : IsHermKernel absRat := fun m => by
  simp [absRat, abs_neg]

theorem isHermKernel_negAbsRat : IsHermKernel negAbsRat := fun m => by
  simp [negAbsRat, isHermKernel_absRat m]

/-- A family of rationals becomes integral after one positive scaling. -/
theorem exists_int_scaling {n : ℕ} (x : Fin n → Multiplicative ℚ) :
    ∃ (D : ℕ) (X : Fin n → Multiplicative ℤ), 0 < D ∧
      ∀ a, ((Multiplicative.toAdd (X a) : ℤ) : ℚ) = D * Multiplicative.toAdd (x a) := by
  set D := ∏ a, (Multiplicative.toAdd (x a)).den
  have hD : 0 < D := Finset.prod_pos fun a _ => (Multiplicative.toAdd (x a)).den_pos
  refine ⟨D, fun a => Multiplicative.ofAdd ((Multiplicative.toAdd (x a)).num *
    ((D / (Multiplicative.toAdd (x a)).den : ℕ) : ℤ)), hD, fun a => ?_⟩
  set q := Multiplicative.toAdd (x a)
  have hdvd : q.den ∣ D := Finset.dvd_prod_of_mem (fun a => (Multiplicative.toAdd (x a)).den)
    (mem_univ a)
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  rw [toAdd_ofAdd]
  set k := D / q.den
  have hk : (k : ℚ) * q.den = D := by exact_mod_cast Nat.div_mul_cancel hdvd
  push_cast
  rw [← hk, mul_assoc, mul_comm (q.den : ℚ) q, Rat.mul_den_eq_num]
  ring

/-- The Gram matrices of `−|b|` on `ℚ` are positive multiples of Gram matrices of `−|m|` on `ℤ`. -/
theorem exists_gram_negAbsRat_eq {n : ℕ} (x : Fin n → Multiplicative ℚ) :
    ∃ (D : ℕ) (X : Fin n → Multiplicative ℤ), 0 < D ∧
      (∀ a b, X a = X b → x a = x b) ∧
      gram negAbsRat x = (((D : ℝ)⁻¹ : ℝ) : ℂ) • gram negAbsKernel X := by
  obtain ⟨D, X, hD, hX⟩ := exists_int_scaling x
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨D, X, hD, fun a b h => ?_, ?_⟩
  · have h1 := hX a
    rw [h, hX b] at h1
    exact Multiplicative.toAdd.injective (mul_left_cancel₀ hDq h1).symm
  · ext a b
    simp only [gram, negAbsRat, absRat, negAbsKernel, Matrix.smul_apply, smul_eq_mul, toAdd_mul,
      toAdd_inv]
    have e : ((|Multiplicative.toAdd (X b) - Multiplicative.toAdd (X a)| : ℤ) : ℚ) =
        D * |Multiplicative.toAdd (x b) - Multiplicative.toAdd (x a)| := by
      push_cast
      rw [hX a, hX b, ← mul_sub, abs_mul, abs_of_pos (by exact_mod_cast hD : (0 : ℚ) < D)]
    have e' : ((|Multiplicative.toAdd (X b) - Multiplicative.toAdd (X a)| : ℤ) : ℂ) =
        ((D * |Multiplicative.toAdd (x b) - Multiplicative.toAdd (x a)| : ℚ) : ℂ) := by
      rw [← e, Rat.cast_intCast]
    have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [neg_add_eq_sub, neg_add_eq_sub, e']
    push_cast
    field_simp

/-- **`−|b|` is conditionally positive on `ℚ`.** -/
theorem hermQuad_gram_negAbsRat_nonneg {n : ℕ} (x : Fin n → Multiplicative ℚ) (c : Fin n → ℂ)
    (hc : ∑ a, c a = 0) : 0 ≤ hermQuad (gram negAbsRat x) c := by
  obtain ⟨D, X, hD, -, hgram⟩ := exists_gram_negAbsRat_eq x
  rw [hgram, hermQuad_smul]
  exact mul_nonneg (by positivity) (hermQuad_gram_negAbsKernel_nonneg X c hc)

theorem polarIndex_negAbsRat : polarIndex negAbsRat = 0 := by
  refine nonpos_iff_eq_zero.mp (iSup₂_le fun n x => ?_)
  rw [negIndexOn_eq_zero_of_nonneg fun c hc => hermQuad_gram_negAbsRat_nonneg x c hc]
  rfl

/-- **`−|b|` has exactly one negative square.** -/
theorem negIndex_negAbsRat : negIndex negAbsRat = 1 := by
  refine le_antisymm ?_ ?_
  · simpa [polarIndex_negAbsRat] using negIndex_le_polarIndex_add_one negAbsRat
  · have hneg : hermQuad (gram negAbsRat ![1, Multiplicative.ofAdd 1]) ![1, 1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, negAbsRat, absRat]
    simpa using card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h

/-- **`−|m|` is strictly conditionally positive on distinct integers**: a nonzero vector of total
mass zero has positive form. The tail sums `Σ_{w_a > t} c_a` determine `c` on distinct points. -/
theorem hermQuad_gram_negAbsKernel_pos {n : ℕ} {X : Fin n → Multiplicative ℤ}
    (hX : Function.Injective X) {c : Fin n → ℂ} (hc : ∑ a, c a = 0) (hc0 : c ≠ 0) :
    0 < hermQuad (gram negAbsKernel X) c := by
  obtain ⟨w, hw, h⟩ := hermQuad_gram_negAbsKernel_eq X c hc
  have hwinj : Function.Injective w := fun a b hab => hX (Multiplicative.toAdd.injective (by
    have := hw a b
    rw [hab, sub_self] at this
    linarith))
  rw [h]
  set S : ℕ → ℂ := fun t => ∑ a, if t < w a then c a else 0
  by_contra hle
  push Not at hle
  have hsum0 : ∑ t ∈ range (∑ b, w b), normSq (S t) = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun t _ => Complex.normSq_nonneg _)
  have hS : ∀ t, S t = 0 := by
    intro t
    by_cases ht : t < ∑ b, w b
    · exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
        fun t _ => Complex.normSq_nonneg _).mp hsum0 t (mem_range.mpr ht))
    · refine Finset.sum_eq_zero fun a _ => if_neg ?_
      have := Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ a)
      omega
  apply hc0
  funext a
  have hsingle : ∀ v : ℕ, w a = v → ∑ b, (if w b = v then c b else 0) = c a := by
    intro v hv
    rw [Finset.sum_eq_single a]
    · rw [if_pos hv]
    · intro b _ hb
      rw [if_neg]
      intro hbv
      exact hb (hwinj (hbv.trans hv.symm))
    · exact fun h => absurd (mem_univ a) h
  rcases Nat.eq_zero_or_eq_succ_pred (w a) with h0 | hk
  · -- the point at the bottom: total mass minus the tail above `0`
    have e : ∑ b, c b = ∑ b, (if w b = 0 then c b else 0) + S 0 := by
      rw [← Finset.sum_add_distrib]
      refine sum_congr rfl fun b _ => ?_
      rcases Nat.eq_zero_or_pos (w b) with hb | hb
      · simp [hb]
      · simp [Nat.pos_iff_ne_zero.mp hb, hb]
    rw [hc, hS 0, add_zero, hsingle 0 h0] at e
    exact e.symm
  · -- two consecutive tail sums differ by the coefficient at `w a`
    set k := (w a).pred
    have e : S k - S (k + 1) = ∑ b, (if w b = k + 1 then c b else 0) := by
      simp only [S, ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun b _ => ?_
      by_cases h1 : w b = k + 1
      · simp [h1]
      · by_cases h2 : k + 1 < w b
        · simp [h1, h2, show k < w b by omega]
        · simp [h1, h2, show ¬ k < w b by omega]
    rw [hS, hS, sub_zero, hsingle (k + 1) hk] at e
    exact e.symm

/-- **`|b|` is negative definite on the polar hyperplane of distinct points.** -/
theorem hermQuad_gram_absRat_neg {n : ℕ} {x : Fin n → Multiplicative ℚ}
    (hx : Function.Injective x) {c : Fin n → ℂ} (hc : ∑ a, c a = 0) (hc0 : c ≠ 0) :
    hermQuad (gram absRat x) c < 0 := by
  obtain ⟨D, X, hD, hXx, hgram⟩ := exists_gram_negAbsRat_eq x
  have hXinj : Function.Injective X := fun a b h => hx (hXx a b h)
  have e : gram absRat x = -gram negAbsRat x := by
    ext a b; simp [gram, negAbsRat]
  rw [e, hermQuad_neg, hgram, hermQuad_smul]
  have := hermQuad_gram_negAbsKernel_pos hXinj hc hc0
  have hD' : (0 : ℝ) < (D : ℝ)⁻¹ := by positivity
  nlinarith

/-- The polar hyperplane of `n` coefficients has dimension `n − 1`. -/
theorem finrank_ker_totalMass (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker (totalMass (Fin (n + 1)))) = n := by
  have hsurj : LinearMap.range (totalMass (Fin (n + 1))) = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun z => ⟨fun a => if a = 0 then z else 0, ?_⟩
    simp [totalMass]
  have h := LinearMap.finrank_range_add_finrank_ker (totalMass (Fin (n + 1)))
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h
  omega

/-- **`|b|` has infinitely many negative squares.** -/
theorem negIndex_absRat : negIndex absRat = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  set x : Fin (n + 1) → Multiplicative ℚ := fun a => Multiplicative.ofAdd (a : ℚ)
  have hx : Function.Injective x := fun a b h => by
    have := congrArg Multiplicative.toAdd h
    simp only [x, toAdd_ofAdd] at this
    exact Fin.ext (by exact_mod_cast this)
  have hpos : IsPosDefOn (-gram absRat x) (LinearMap.ker (totalMass (Fin (n + 1)))) := by
    intro c hc hc0
    rw [hermQuad_neg]
    have := hermQuad_gram_absRat_neg hx (c := c) hc hc0
    linarith
  have h := finrank_le_posIndex hpos
  rw [finrank_ker_totalMass] at h
  exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex absRat x)

/-- A positive multiple of a kernel has the same index. -/
theorem negIndex_ofReal_mul {G : Type*} [Group G] (k : G → ℂ) {r : ℝ} (hr : 0 < r) :
    negIndex (fun g => (r : ℂ) * k g) = negIndex k := by
  have e : ∀ (n : ℕ) (x : Fin n → G), gram (fun g => (r : ℂ) * k g) x = (r : ℂ) • gram k x :=
    fun n x => by ext a b; simp [gram]
  have h : ∀ (n : ℕ) (x : Fin n → G),
      HTGeometry.hermNegIndex (gram (fun g => (r : ℂ) * k g) x) =
        HTGeometry.hermNegIndex (gram k x) := fun n x => by
    rw [e n x]
    show hermPosIndex (-((r : ℂ) • gram k x)) = hermPosIndex (-gram k x)
    rw [← smul_neg, posIndex_smul_pos hr]
  unfold HeckeKreinToeplitz.negIndex
  simp_rw [h]

/-- **The conformal successors of exponent one.** The successor `c|b|`, on which the dilation by `u`
acts with conformal factor `|u|`, has index `0` for `c = 0`, `1` for `c < 0` and `∞` for `c > 0`. -/
theorem negIndex_mul_absRat (c : ℝ) :
    negIndex (fun m => (c : ℂ) * absRat m) = if c = 0 then 0 else if c < 0 then 1 else ⊤ := by
  split_ifs with h0 hneg
  · subst h0
    refine negIndex_eq_zero_iff.mpr fun n x c => ?_
    have hz : gram (fun m => ((0 : ℝ) : ℂ) * absRat m) x = 0 := by ext a b; simp [gram]
    rw [hz]
    simp [hermQuad]
  · have e : (fun m => (c : ℂ) * absRat m) = fun m => ((-c : ℝ) : ℂ) * negAbsRat m := by
      funext m; simp [negAbsRat]
    rw [e, negIndex_ofReal_mul _ (by linarith), negIndex_negAbsRat]
  · rw [negIndex_ofReal_mul _ (lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm h0)), negIndex_absRat]

end GaloisForLFunctions.AdelicKreinGeometry
