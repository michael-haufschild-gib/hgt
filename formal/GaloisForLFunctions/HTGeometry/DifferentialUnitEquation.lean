import Mathlib

/-!
# The differential unit equation: no rational logarithmic derivative equals `m·u`

The differential analogue of the shift eigenrelation (`no_shift_eigenrelation`).  On the
differential polynomial ring `ℂ{u} = MvPolynomial ℕ ℂ` — jet coordinates `x₀ = s`,
`x₁ = u`, `x_{j+1} = u⁽ʲ⁾` — with the total derivative `𝒟` (`𝒟 x₀ = 1`, `𝒟 x_k = x_{k+1}`
for `k ≥ 1`), the **differential unit equation** is

`𝒟 w = m · x₁ · w`,  `m ≥ 1`.

It has no nonzero solution in the fraction field.  In cross-multiplied polynomial form: for
coprime `p, q ≠ 0`,

`𝒟p · q − p · 𝒟q = m · x₁ · p · q`

is impossible (`differential_unit_no_go`); dropping coprimality
(`no_differential_eigenrelation`) it is the terminal obstruction of the logarithmic
derivative closure of differential algebraicity — eliminating an `f`-power relation for a
differentially algebraic `f` against `f' = u·f`, differentiation contributing the factor
`d` in `f`-degree `d`, leaves exactly this identity, with `u = f'/f = x₁`.

The proof is the differential twin of the shift no-go's integer-root pinch.  The total
derivative introduces, at the top jet variable `x_N`, a fresh variable `x_{N+1}` linearly
with coefficient `∂_{x_N}`; applying `∂_{x_{N+1}}` to the equation and using coprimality
plus the strict total-degree drop of `∂_{x_N}` forces `p, q` independent of `x_N`.
Descending to `ℂ[x₀]`, a final `∂_{x₁}` reads off `m·p·q = 0`, impossible.

* `totalDeriv` — the total derivative derivation.
* `pderiv_succ_totalDeriv`, `pderiv_one_totalDeriv` — the two commutator identities.
* `totalDegree_pderiv_lt`, `pderiv_ne_zero_of_mem_vars`, `pderiv_self_dvd_eq_zero` — helpers.
* `differential_unit_no_go`, `no_differential_eigenrelation` — the obstruction.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

/-! ## The total derivative -/

/-- The images of the jet generators under the total derivative: `x₀ ↦ 1`,
`x_k ↦ x_{k+1}` for `k ≥ 1`. -/
def totalDerivGen : ℕ → MvPolynomial ℕ ℂ := fun n => if n = 0 then 1 else X (n + 1)

theorem totalDerivGen_zero : totalDerivGen 0 = 1 := rfl

theorem totalDerivGen_succ (n : ℕ) : totalDerivGen (n + 1) = X (n + 2) := by
  simp [totalDerivGen]

/-- The **total derivative** on the differential polynomial ring `ℂ{u} = MvPolynomial ℕ ℂ`:
the `ℂ`-derivation with `x₀ ↦ 1` and `x_k ↦ x_{k+1}` for `k ≥ 1`. -/
def totalDeriv : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  mkDerivation ℂ totalDerivGen

theorem totalDeriv_X (n : ℕ) : totalDeriv (X n) = totalDerivGen n := by
  rw [totalDeriv, mkDerivation_X]

theorem totalDeriv_C (a : ℂ) : totalDeriv (C a) = 0 := derivation_C totalDeriv a

/-- Local abbreviation pinning the `ℂ`-derivation type of `pderiv` (needed for the Lie
bracket). -/
private abbrev DD (n : ℕ) : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) := pderiv n

/-! ## The commutator identities -/

/-- `[∂_{x_{N+1}}, 𝒟] = ∂_{x_N}` for `N ≥ 1`. -/
theorem pderiv_succ_totalDeriv {N : ℕ} (hN : 1 ≤ N) (p : MvPolynomial ℕ ℂ) :
    pderiv (N + 1) (totalDeriv p)
      = totalDeriv (pderiv (N + 1) p) + pderiv N p := by
  have hcomm : ⁅DD (N + 1), totalDeriv⁆ = pderiv N := by
    apply derivation_ext
    intro i
    have hk : ⁅DD (N + 1), totalDeriv⁆ (X i)
        = pderiv (N + 1) (totalDeriv (X i)) - totalDeriv (pderiv (N + 1) (X i)) :=
      Derivation.commutator_apply (X i)
    rw [hk, totalDeriv_X]
    have h2 : totalDeriv (pderiv (N + 1) (X i)) = 0 := by
      by_cases hi : i = N + 1
      · rw [hi, pderiv_X_self, Derivation.map_one_eq_zero]
      · rw [pderiv_X_of_ne hi, map_zero]
    rw [h2, sub_zero]
    rcases i with _ | k
    · rw [totalDerivGen_zero, Derivation.map_one_eq_zero,
        pderiv_X_of_ne (by omega : (0 : ℕ) ≠ N)]
    · rw [totalDerivGen_succ]
      by_cases hk2 : N = k + 1
      · subst hk2; rw [pderiv_X_self, pderiv_X_self]
      · rw [pderiv_X_of_ne (by omega : k + 2 ≠ N + 1),
          pderiv_X_of_ne (by omega : k + 1 ≠ N)]
  have hkp : ⁅DD (N + 1), totalDeriv⁆ p
      = pderiv (N + 1) (totalDeriv p) - totalDeriv (pderiv (N + 1) p) :=
    Derivation.commutator_apply p
  rw [hcomm] at hkp
  linear_combination -hkp

/-- `[∂_{x₁}, 𝒟] = 0`. -/
theorem pderiv_one_totalDeriv (p : MvPolynomial ℕ ℂ) :
    pderiv 1 (totalDeriv p) = totalDeriv (pderiv 1 p) := by
  have hcomm : ⁅DD 1, totalDeriv⁆ = 0 := by
    apply derivation_ext
    intro i
    have hk : ⁅DD 1, totalDeriv⁆ (X i)
        = pderiv 1 (totalDeriv (X i)) - totalDeriv (pderiv 1 (X i)) :=
      Derivation.commutator_apply (X i)
    rw [hk, totalDeriv_X, Derivation.zero_apply]
    have h2 : totalDeriv (pderiv 1 (X i)) = 0 := by
      by_cases hi : i = 1
      · rw [hi, pderiv_X_self, Derivation.map_one_eq_zero]
      · rw [pderiv_X_of_ne hi, map_zero]
    rw [h2, sub_zero]
    rcases i with _ | k
    · rw [totalDerivGen_zero, Derivation.map_one_eq_zero]
    · rw [totalDerivGen_succ, pderiv_X_of_ne (by omega : k + 2 ≠ 1)]
  have hkp : ⁅DD 1, totalDeriv⁆ p
      = pderiv 1 (totalDeriv p) - totalDeriv (pderiv 1 p) := Derivation.commutator_apply p
  rw [hcomm, Derivation.zero_apply] at hkp
  linear_combination -hkp

/-! ## Degree and variable helpers -/

/-- A partial derivative strictly lowers the total degree. -/
theorem totalDegree_pderiv_lt {i : ℕ} {p : MvPolynomial ℕ ℂ} (h : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hsum : pderiv i p
      = ∑ s ∈ p.support, monomial (s - Finsupp.single i 1) (coeff s p * (s i : ℂ)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => pderiv_monomial
  have hex : ∃ s ∈ p.support, 1 ≤ s i := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    apply h
    rw [hsum]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [Nat.lt_one_iff.mp (hcon s hs), Nat.cast_zero, mul_zero, monomial_zero]
  obtain ⟨s₀, hs₀, hs₀i⟩ := hex
  have hs₀sum : 1 ≤ s₀.sum (fun _ e => e) :=
    le_trans hs₀i (Finset.single_le_sum (f := fun j => s₀ j)
      (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr (by omega)))
  have hppos : 1 ≤ p.totalDegree := le_trans hs₀sum (le_totalDegree hs₀)
  have hbound : (∑ s ∈ p.support,
      monomial (s - Finsupp.single i 1) (coeff s p * (s i : ℂ))).totalDegree
      ≤ p.totalDegree - 1 := by
    apply totalDegree_finsetSum_le
    intro s hs
    by_cases hsi : s i = 0
    · rw [hsi, Nat.cast_zero, mul_zero, monomial_zero, totalDegree_zero]
      omega
    · refine le_trans (totalDegree_monomial_le _ _) ?_
      have hsub : (s - Finsupp.single i 1).sum (fun _ e => e) + 1
          = s.sum (fun _ e => e) := by
        conv_rhs => rw [show s = (s - Finsupp.single i 1) + Finsupp.single i 1 from by
          ext j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hj : i = j
          · subst hj; rw [if_pos rfl]; omega
          · rw [if_neg hj]; omega]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      have hle : s.sum (fun _ e => e) ≤ p.totalDegree := le_totalDegree hs
      have hid : (s - Finsupp.single i 1).sum (fun _ e => id e)
          = (s - Finsupp.single i 1).sum (fun _ e => e) := rfl
      rw [hid]
      omega
  rw [hsum]; omega

/-- Over a domain, a polynomial dividing its own partial derivative kills it. -/
theorem pderiv_self_dvd_eq_zero {i : ℕ} {p : MvPolynomial ℕ ℂ}
    (hdvd : p ∣ pderiv i p) : pderiv i p = 0 := by
  by_contra h
  have h1 := totalDegree_pderiv_lt h
  have h2 := totalDegree_le_of_dvd_of_isDomain hdvd h
  omega

/-- A variable appearing in `p` has a nonzero partial derivative (characteristic zero). -/
theorem pderiv_ne_zero_of_mem_vars {i : ℕ} {p : MvPolynomial ℕ ℂ} (hi : i ∈ p.vars) :
    pderiv i p ≠ 0 := by
  classical
  obtain ⟨s₀, hs₀, hs₀i⟩ := (mem_vars_iff_mem_support i).mp hi
  have hsi : 1 ≤ s₀ i := by rw [Finsupp.mem_support_iff] at hs₀i; omega
  intro h
  have hsum : X i * pderiv i p
      = ∑ s ∈ p.support, (s i) • monomial s (coeff s p) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => X_mul_pderiv_monomial
  have hco : coeff s₀ (X i * pderiv i p) = (s₀ i) • coeff s₀ p := by
    rw [hsum, coeff_sum, Finset.sum_eq_single s₀]
    · rw [coeff_smul, coeff_monomial, if_pos rfl]
    · intro s _ hne
      rw [coeff_smul, coeff_monomial, if_neg hne, smul_zero]
    · intro hns₀
      rw [coeff_smul, coeff_monomial, if_pos rfl,
        MvPolynomial.notMem_support_iff.mp hns₀, smul_zero]
  rw [h, mul_zero, coeff_zero] at hco
  have hne : (s₀ i) • coeff s₀ p ≠ 0 := by
    rw [nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hsi)
      (MvPolynomial.mem_support_iff.mp hs₀)
  exact hne hco.symm

/-! ## The differential unit equation -/

/-- **The differential unit equation has no coprime solution.**  For coprime `p, q ≠ 0` and
`m ≥ 1`, the identity `𝒟p·q − p·𝒟q = m·x₁·p·q` is impossible. -/
theorem differential_unit_no_go {p q : MvPolynomial ℕ ℂ} (hco : IsRelPrime p q)
    (hp : p ≠ 0) (hq : q ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (h : totalDeriv p * q - p * totalDeriv q
      = C (m : ℂ) * X 1 * (p * q)) : False := by
  classical
  have hCm : (C (m : ℂ) : MvPolynomial ℕ ℂ) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  by_cases hcase : ∀ i ∈ p.vars ∪ q.vars, i = 0
  · -- every variable is `x₀`: a final `∂_{x₁}` reads off `m·p·q = 0`
    have hp1 : pderiv 1 p = 0 :=
      pderiv_eq_zero_of_notMem_vars fun hin => by
        have := hcase 1 (Finset.mem_union_left _ hin); omega
    have hq1 : pderiv 1 q = 0 :=
      pderiv_eq_zero_of_notMem_vars fun hin => by
        have := hcase 1 (Finset.mem_union_right _ hin); omega
    have hlhs : pderiv 1 (totalDeriv p * q - p * totalDeriv q) = 0 := by
      rw [map_sub, pderiv_mul, pderiv_mul, pderiv_one_totalDeriv, pderiv_one_totalDeriv,
        hp1, hq1]
      simp
    have hrhs : pderiv 1 (C (m : ℂ) * X 1 * (p * q)) = C (m : ℂ) * (p * q) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul, pderiv_X_self, pderiv_mul, hp1, hq1]
      ring
    have hd := congrArg (pderiv 1) h
    rw [hlhs, hrhs] at hd
    exact (mul_ne_zero hCm (mul_ne_zero hp hq)) hd.symm
  · -- some variable `N ≥ 1`: pinch the top variable
    simp only [not_forall] at hcase
    obtain ⟨i₀, hi₀mem, hi₀⟩ := hcase
    set S := p.vars ∪ q.vars with hS
    have hSne : S.Nonempty := ⟨i₀, hi₀mem⟩
    set N := S.max' hSne with hN
    have hN1 : 1 ≤ N := le_trans (Nat.one_le_iff_ne_zero.mpr hi₀) (S.le_max' i₀ hi₀mem)
    have hNmem : N ∈ S := S.max'_mem hSne
    have hNp1notin : N + 1 ∉ S := fun hin => by have := S.le_max' (N + 1) hin; omega
    have hp1 : pderiv (N + 1) p = 0 :=
      pderiv_eq_zero_of_notMem_vars fun hin => hNp1notin (Finset.mem_union_left _ hin)
    have hq1 : pderiv (N + 1) q = 0 :=
      pderiv_eq_zero_of_notMem_vars fun hin => hNp1notin (Finset.mem_union_right _ hin)
    have hlhs : pderiv (N + 1) (totalDeriv p * q - p * totalDeriv q)
        = pderiv N p * q - p * pderiv N q := by
      rw [map_sub, pderiv_mul, pderiv_mul, pderiv_succ_totalDeriv hN1,
        pderiv_succ_totalDeriv hN1, hp1, hq1]
      simp
    have hrhs : pderiv (N + 1) (C (m : ℂ) * X 1 * (p * q)) = 0 := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul,
        pderiv_X_of_ne (by omega : (1 : ℕ) ≠ N + 1), pderiv_mul, hp1, hq1]
      simp
    have hd := congrArg (pderiv (N + 1)) h
    rw [hlhs, hrhs] at hd
    have heq : pderiv N p * q = p * pderiv N q := sub_eq_zero.mp hd
    have hdvdp : p ∣ pderiv N p :=
      hco.dvd_of_dvd_mul_right ⟨pderiv N q, by rw [heq]⟩
    have hpN : pderiv N p = 0 := pderiv_self_dvd_eq_zero hdvdp
    have hdvdq : q ∣ pderiv N q :=
      hco.symm.dvd_of_dvd_mul_right ⟨pderiv N p, by rw [mul_comm, ← heq, mul_comm]⟩
    have hqN : pderiv N q = 0 := pderiv_self_dvd_eq_zero hdvdq
    rw [hS, Finset.mem_union] at hNmem
    rcases hNmem with hmemp | hmemq
    · exact pderiv_ne_zero_of_mem_vars hmemp hpN
    · exact pderiv_ne_zero_of_mem_vars hmemq hqN

/-- **The differential eigenrelation is impossible.**  Dropping coprimality: for any
`p, q ≠ 0` and `m ≥ 1`, `𝒟p·q − p·𝒟q = m·x₁·p·q` fails.  Reducing to relatively prime
parts — the logarithmic-derivative eigenrelation is invariant under common factors —
returns the coprime no-go. -/
theorem no_differential_eigenrelation {p q : MvPolynomial ℕ ℂ}
    (hp : p ≠ 0) (hq : q ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (h : totalDeriv p * q - p * totalDeriv q
      = C (m : ℂ) * X 1 * (p * q)) : False := by
  classical
  obtain ⟨p₀, q₀, c, hco, hcp, hcq⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors p hp q
  have hc : c ≠ 0 := fun h0 => hp (by rw [← hcp, h0, zero_mul])
  have hp₀ : p₀ ≠ 0 := fun h0 => hp (by rw [← hcp, h0, mul_zero])
  have hq₀ : q₀ ≠ 0 := fun h0 => hq (by rw [← hcq, h0, mul_zero])
  refine differential_unit_no_go hco hp₀ hq₀ hm ?_
  have hexp : (c * c) * (totalDeriv p₀ * q₀ - p₀ * totalDeriv q₀)
      = (c * c) * (C (m : ℂ) * X 1 * (p₀ * q₀)) := by
    have hL : totalDeriv p * q - p * totalDeriv q
        = (c * c) * (totalDeriv p₀ * q₀ - p₀ * totalDeriv q₀) := by
      rw [← hcp, ← hcq]
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    have hR : C (m : ℂ) * X 1 * (p * q)
        = (c * c) * (C (m : ℂ) * X 1 * (p₀ * q₀)) := by
      rw [← hcp, ← hcq]; ring
    rw [← hL, ← hR]; exact h
  exact mul_left_cancel₀ (mul_ne_zero hc hc) hexp

end GaloisForLFunctions

end
