import GaloisForLFunctions.RHTower.Matveev.FeldmanJetPolynomials
import GaloisForLFunctions.RHTower.Matveev.LinearFormBasic

/-!
# Fel'dman's auxiliary function for a linear form in prime logarithms

Let `p₀, …, p_m` be primes and `Λ = Σ_j b_j log p_j` with integer coefficients, the last one
`B = b_m > 0` the largest in absolute value.  For an exponent vector `l ∈ ℕ^{m+1}` put

`γ_j(l) = B l_j − b_j l_m`,  `ω′(l) = Σ_{j<m} (γ_j(l)/B) log p_j`,  `ω(l) = Σ_j l_j log p_j`,

so that `ω′(l) = ω(l) − l_m Λ / B`: the frequency `ω′` has the relation `B log p_m = −Σ_{j<m} b_j
log p_j` built in, and differs from the true frequency only by a multiple of `Λ`.

With integer coefficients `C(k, l)` (`k ≤ N`, `l ∈ [0, q)^{m+1}`) the auxiliary functions are

`F_{σ,τ}(z) = Σ C(k,l) g_k^{[σ]}(z) ∏_{j<m} (γ_j/B)^{τ_j} e^{z ω′(l)}`,
`Φ_{σ,τ}(z) = Σ C(k,l) g_k^{[σ]}(z) ∏_{j<m} (γ_j/B)^{τ_j} e^{z ω(l)}`.

`F_{σ,τ}` is the diagonal restriction of the `(σ, τ)`-derivative of a function of `m + 1` variables,
so `F′_{σ,τ} = (σ+1) F_{σ+1,τ} + Σ_j log p_j F_{σ,τ+e_j}`.  At a natural number `x` the value
`Φ_{σ,τ}(x)` is arithmetic: `B^{|τ|} Φ_{σ,τ}(x) = D · A_{σ,τ}(x)` with `A_{σ,τ}(x) ∈ ℤ` and `D`
Fel'dman's common divisor, while `|F_{σ,τ} − Φ_{σ,τ}|` is a multiple of `|Λ|`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Complex

variable {m : ℕ} (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)

/-- The integer numerators `γ_j(l) = B l_j − b_j l_m` of the perturbed frequency coordinates. -/
def feldmanGamma (l : Fin (m + 1) → ℕ) (j : Fin m) : ℤ :=
  b (Fin.last m) * (l j.castSucc : ℤ) - b j.castSucc * (l (Fin.last m) : ℤ)

/-- The perturbed frequency `ω′(l) = Σ_{j<m} (γ_j(l)/B) log p_j`. -/
def feldmanFreq (l : Fin (m + 1) → ℕ) : ℝ :=
  ∑ j : Fin m, (feldmanGamma b l j : ℝ) / (b (Fin.last m) : ℝ) * Real.log (p j.castSucc)

/-- The true frequency `ω(l) = Σ_j l_j log p_j`. -/
def trueFreq (l : Fin (m + 1) → ℕ) : ℝ := ∑ j, (l j : ℝ) * Real.log (p j)

/-- `ω′(l) = ω(l) − l_m Λ / B`. -/
theorem feldmanFreq_eq (hB : b (Fin.last m) ≠ 0) (l : Fin (m + 1) → ℕ) :
    feldmanFreq p b l =
      trueFreq p l - (l (Fin.last m) : ℝ) * primeLogForm p b / (b (Fin.last m) : ℝ) := by
  have hBr : (b (Fin.last m) : ℝ) ≠ 0 := by exact_mod_cast hB
  have hterm : ∀ j : Fin m,
      (feldmanGamma b l j : ℝ) / (b (Fin.last m) : ℝ) * Real.log (p j.castSucc) =
        (l j.castSucc : ℝ) * Real.log (p j.castSucc) -
          (l (Fin.last m) : ℝ) / (b (Fin.last m) : ℝ) *
            ((b j.castSucc : ℝ) * Real.log (p j.castSucc)) := by
    intro j
    rw [feldmanGamma]
    push_cast
    field_simp
  unfold feldmanFreq trueFreq primeLogForm
  rw [sum_congr rfl (fun j _ => hterm j), sum_sub_distrib, ← mul_sum,
    Fin.sum_univ_castSucc (fun j => (l j : ℝ) * Real.log (p j)),
    Fin.sum_univ_castSucc (fun i => (b i : ℝ) * Real.log (p i))]
  field_simp
  ring

/-- The index set of the unknowns: a Lagrange index `k ≤ N` and an exponent box vector. -/
abbrev FeldmanIndex (N q m : ℕ) := Fin (N + 1) × (Fin (m + 1) → Fin q)

/-- The exponent vector of an index. -/
def FeldmanIndex.expo {N q : ℕ} (kl : FeldmanIndex N q m) : Fin (m + 1) → ℕ :=
  fun i => (kl.2 i : ℕ)

/-- The weight `∏_{j<m} (γ_j/B)^{τ_j}`. -/
def gammaWeight (l : Fin (m + 1) → ℕ) (τ : Fin m → ℕ) : ℂ :=
  ∏ j, ((feldmanGamma b l j : ℂ) / (b (Fin.last m) : ℂ)) ^ τ j

/-- **Fel'dman's auxiliary function** `F_{σ,τ}`. -/
def feldmanAux (N q : ℕ) (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin m → ℕ) (z : ℂ) : ℂ :=
  ∑ kl, (C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo τ *
    Complex.exp (z * (feldmanFreq p b kl.expo : ℂ))

/-- The companion `Φ_{σ,τ}` with the true frequencies. -/
def feldmanTrueAux (N q : ℕ) (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin m → ℕ) (z : ℂ) :
    ℂ :=
  ∑ kl, (C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo τ *
    Complex.exp (z * (trueFreq p kl.expo : ℂ))

/-- The integer value `A_{σ,τ}(x)`. -/
def feldmanArith (N q S : ℕ) (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin m → ℕ) (x : ℕ) :
    ℤ :=
  ∑ kl, C kl * ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℤ) *
    (∏ j, feldmanGamma b kl.expo j ^ τ j) * ∏ j, (p j : ℤ) ^ (kl.expo j * x)

/-- At a natural number the true exponential is an `S`-unit. -/
theorem exp_natCast_mul_trueFreq (hp : ∀ j, 0 < p j) (l : Fin (m + 1) → ℕ) (x : ℕ) :
    Complex.exp ((x : ℂ) * (trueFreq p l : ℂ)) = ((∏ j, (p j : ℤ) ^ (l j * x) : ℤ) : ℂ) := by
  have hreal : Real.exp ((x : ℝ) * trueFreq p l) = ∏ j, (p j : ℝ) ^ (l j * x) := by
    rw [trueFreq, mul_sum, Real.exp_sum]
    refine prod_congr rfl fun j _ => ?_
    rw [show (x : ℝ) * ((l j : ℝ) * Real.log (p j)) = ((l j * x : ℕ) : ℝ) * Real.log (p j) by
      push_cast; ring, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hp j)]
  have := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_prod, Complex.ofReal_pow] at this
  rw [this]
  push_cast
  rfl

/-- `B^{|τ|}` times the weight is the integer `∏ γ_j^{τ_j}`. -/
theorem pow_mul_gammaWeight (hB : b (Fin.last m) ≠ 0) (l : Fin (m + 1) → ℕ) (τ : Fin m → ℕ) :
    (b (Fin.last m) : ℂ) ^ (∑ j, τ j) * gammaWeight b l τ =
      ((∏ j, feldmanGamma b l j ^ τ j : ℤ) : ℂ) := by
  have hBc : (b (Fin.last m) : ℂ) ≠ 0 := by exact_mod_cast hB
  rw [gammaWeight, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  push_cast
  refine prod_congr rfl fun j _ => ?_
  rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hBc)]

/-- **The arithmetic relation.**  `B^{|τ|} Φ_{σ,τ}(x) = D · A_{σ,τ}(x)` for `σ < S`. -/
theorem pow_mul_feldmanTrueAux_natCast (hp : ∀ j, 0 < p j) (hB : b (Fin.last m) ≠ 0)
    {N q S : ℕ} (C : FeldmanIndex N q m → ℤ) {σ : ℕ} (hσS : σ < S) (τ : Fin m → ℕ) (x : ℕ) :
    (b (Fin.last m) : ℂ) ^ (∑ j, τ j) * feldmanTrueAux p b N q C σ τ (x : ℂ) =
      (feldmanDivisor (N + 1) S : ℂ) * (feldmanArith p b N q S C σ τ x : ℂ) := by
  rw [feldmanTrueAux, feldmanArith, mul_sum, Int.cast_sum, mul_sum]
  refine sum_congr rfl fun kl _ => ?_
  have hk : (kl.1 : ℕ) ≤ N := Nat.lt_succ_iff.mp kl.1.isLt
  have hjet : feldmanJet N kl.1 σ (x : ℂ) =
      (feldmanDivisor (N + 1) S : ℂ) *
        ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℂ) := by
    rw [feldmanJet_natCast hk, ← Nat.cast_mul,
      Nat.mul_div_cancel' (feldmanDivisor_dvd_feldmanJetNat hσS x)]
  rw [hjet, exp_natCast_mul_trueFreq p hp kl.expo x]
  have hw := pow_mul_gammaWeight b hB kl.expo τ
  generalize (feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S) = jd
  generalize gammaWeight b kl.expo τ = w at hw ⊢
  push_cast at hw ⊢
  linear_combination ((C kl : ℂ) * (feldmanDivisor (N + 1) S : ℂ) * (jd : ℂ) *
    ∏ j, ((p j : ℂ) ^ (kl.expo j * x))) * hw

/-! ## The derivative identity -/

/-- Raising one exponent multiplies the weight by the corresponding coordinate. -/
theorem gammaWeight_add_single (l : Fin (m + 1) → ℕ) (τ : Fin m → ℕ) (j : Fin m) :
    gammaWeight b l (τ + Pi.single j 1) =
      gammaWeight b l τ * ((feldmanGamma b l j : ℂ) / (b (Fin.last m) : ℂ)) := by
  classical
  rw [gammaWeight, gammaWeight]
  simp only [Pi.add_apply, pow_add]
  rw [prod_mul_distrib]
  congr 1
  rw [prod_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, pow_zero])
    (fun h => absurd (mem_univ j) h)]
  simp

theorem hasDerivAt_feldmanAux {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin m → ℕ)
    (z : ℂ) :
    HasDerivAt (feldmanAux p b N q C σ τ)
      (((σ : ℂ) + 1) * feldmanAux p b N q C (σ + 1) τ z +
        ∑ j : Fin m, (Real.log (p j.castSucc) : ℂ) *
          feldmanAux p b N q C σ (τ + Pi.single j 1) z) z := by
  unfold feldmanAux
  have hterm : ∀ kl : FeldmanIndex N q m, HasDerivAt
      (fun w => (C kl : ℂ) * feldmanJet N kl.1 σ w * gammaWeight b kl.expo τ *
        Complex.exp (w * (feldmanFreq p b kl.expo : ℂ)))
      ((C kl : ℂ) * (((σ : ℂ) + 1) * feldmanJet N kl.1 (σ + 1) z) * gammaWeight b kl.expo τ *
          Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) +
        (C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo τ *
          (Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) * (feldmanFreq p b kl.expo : ℂ))) z := by
    intro kl
    have h1 := (((hasDerivAt_feldmanJet N kl.1 σ z).const_mul (C kl : ℂ)).mul_const
      (gammaWeight b kl.expo τ))
    have h2 := ((hasDerivAt_id z).mul_const (feldmanFreq p b kl.expo : ℂ)).cexp
    simp only [id, one_mul] at h2
    exact h1.mul h2
  refine (HasDerivAt.fun_sum fun kl _ => hterm kl).congr_deriv ?_
  have hfreq : ∀ kl : FeldmanIndex N q m, (feldmanFreq p b kl.expo : ℂ) =
      ∑ j : Fin m, ((feldmanGamma b kl.expo j : ℂ) / (b (Fin.last m) : ℂ)) *
        (Real.log (p j.castSucc) : ℂ) := by
    intro kl
    rw [feldmanFreq]
    push_cast
    rfl
  calc ∑ kl : FeldmanIndex N q m,
        ((C kl : ℂ) * (((σ : ℂ) + 1) * feldmanJet N kl.1 (σ + 1) z) * gammaWeight b kl.expo τ *
            Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) +
          (C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo τ *
            (Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) * (feldmanFreq p b kl.expo : ℂ)))
      = ∑ kl : FeldmanIndex N q m,
          (((σ : ℂ) + 1) * ((C kl : ℂ) * feldmanJet N kl.1 (σ + 1) z * gammaWeight b kl.expo τ *
              Complex.exp (z * (feldmanFreq p b kl.expo : ℂ))) +
            ∑ j : Fin m, (Real.log (p j.castSucc) : ℂ) *
              ((C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo (τ + Pi.single j 1) *
                Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)))) := by
        refine sum_congr rfl fun kl _ => ?_
        simp only [gammaWeight_add_single]
        set e := Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) with he
        rw [hfreq kl, mul_sum, mul_sum]
        congr 1
        · ring
        · refine sum_congr rfl fun j _ => ?_
          ring
    _ = ((σ : ℂ) + 1) * ∑ kl : FeldmanIndex N q m, (C kl : ℂ) * feldmanJet N kl.1 (σ + 1) z *
            gammaWeight b kl.expo τ * Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) +
          ∑ j : Fin m, (Real.log (p j.castSucc) : ℂ) *
            ∑ kl : FeldmanIndex N q m, (C kl : ℂ) * feldmanJet N kl.1 σ z *
              gammaWeight b kl.expo (τ + Pi.single j 1) *
                Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) := by
        rw [sum_add_distrib, mul_sum]
        congr 1
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_sum]

theorem differentiable_feldmanAux {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ)
    (τ : Fin m → ℕ) : Differentiable ℂ (feldmanAux p b N q C σ τ) :=
  fun z => (hasDerivAt_feldmanAux p b C σ τ z).differentiableAt

theorem deriv_feldmanAux {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin m → ℕ) :
    deriv (feldmanAux p b N q C σ τ) = fun z =>
      ((σ : ℂ) + 1) * feldmanAux p b N q C (σ + 1) τ z +
        ∑ j : Fin m, (Real.log (p j.castSucc) : ℂ) *
          feldmanAux p b N q C σ (τ + Pi.single j 1) z := by
  funext z
  exact (hasDerivAt_feldmanAux p b C σ τ z).deriv

end GaloisForLFunctions.RHTower.Matveev
