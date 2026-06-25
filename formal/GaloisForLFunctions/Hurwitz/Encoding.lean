/-
# Hurwitz N=2 — field encoding: feeding the committed `ζ(s+k,a)` local split into the descent machine

The abstract descent spine (`Hurwitz.Spine`) consumes blocks of the form `∑_w A_w(−n+e^z)·e^{−(2s+w)z}`.
This file connects the *committed* Hurwitz-zeta local split (`HurwitzZeta.hzeta_local_split_shift`,
`F_k = ζ(s+k,−n+x) = x^{−(s+k)} + R_{n,k}(x)`) to that `z = log x` form: on the strip `Im z ∈ (−π,π]`
the singular term `x^{−(s+k)} = (e^z)^{−(s+k)}` becomes `e^{−(s+k)z}` (`cexp_cpow_strip`), and the tail
`R_{n,k}(e^z)` is `2πi`-periodic (`comp_exp_periodic`) — so `F_k` is exactly one singular exponential
`e^{−(s+k)z}` plus a periodic remainder, the shape `block_shift_eigen`/`shift_eigenspace_separation`
separate by monodromy eigenvalue.
-/
import GaloisForLFunctions.Hurwitz.Spine
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import GaloisForLFunctions.Hurwitz.DescentAlgebra

open Complex HurwitzZetaShift HurwitzSpine HurwitzDescent

namespace HurwitzEncoding

/-- **`F_k` in the `z = log x` coordinate (singular exponential + periodic tail).** On the strip
`Im z ∈ (−π, π]`, `ζ(s+k, −n+e^z) = e^{−(s+k)z} + R_{n,k}(e^z)`, where the tail
`R_{n,k}(x) = ∑'_{m≠n} (m−n+x)^{−(s+k)}` is the regular (`2πi`-periodic in `z`) part. This is the entry
point that turns the committed Hurwitz-zeta local expansion into the block form the descent machine
consumes: the lone singular exponent is `−(s+k)`, eigenvalue `e^{−2πis}` under the shift. -/
theorem Fk_zform {s : ℂ} (hs : 1 < s.re) (k n : ℕ) {z : ℂ}
    (h1 : -Real.pi < z.im) (h2 : z.im ≤ Real.pi) :
    hzeta (s + k) (-(n : ℂ) + Complex.exp z)
      = Complex.exp (-(s + (k : ℂ)) * z)
        + ∑' m : ℕ, (if m = n then (0 : ℂ)
            else ((m : ℂ) + (-(n : ℂ) + Complex.exp z)) ^ (-(s + (k : ℂ)))) := by
  rw [hzeta_local_split_shift hs k n (Complex.exp z), cexp_cpow_strip h1 h2]

/-- **Quadratic singular term.** The product of two singular exponentials `e^{−(s+i)z}·e^{−(s+j)z}` is the
single exponential `e^{−(2s+(i+j))z}` — the doubly-singular term whose exponent base is `2s` (eigenvalue
`e^{−4πis}`), i.e. the quadratic block. So `F_i·F_j` contributes its singular part to weight `w = i+j`,
the regrouping `DescentAlgebra.quadratic_weight_regroup` collects (`A_w = ∑_{i+j=w} q_{ij}`). -/
theorem sing_product {s : ℂ} (i j : ℕ) (z : ℂ) :
    Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)
      = Complex.exp (-(2 * s + ((i : ℂ) + (j : ℂ))) * z) := by
  rw [← Complex.exp_add]; ring_nf

/-- **`F_i·F_j` decomposition (singular-quadratic + cross + regular).** Writing `F_k = E_k + R_k` with
`E_k = e^{−(s+k)z}` singular and `R_k` the periodic tail, the product splits into the quadratic singular
`e^{−(2s+(i+j))z}` (eigenvalue `e^{−4πis}`), the cross `E_i R_j + E_j R_i` (singular exponent `−(s+·)`,
eigenvalue `e^{−2πis}` — folded into the linear block), and the regular `R_i R_j` (eigenvalue `1`). After
the quadratic filtration kills every `q_{ij}`, the cross terms vanish and the linear block is clean. -/
theorem FiFj_decomp {s : ℂ} (i j : ℕ) (z : ℂ) (Ri Rj : ℂ) :
    (Complex.exp (-(s + (i : ℂ)) * z) + Ri) * (Complex.exp (-(s + (j : ℂ)) * z) + Rj)
      = Complex.exp (-(2 * s + ((i : ℂ) + (j : ℂ))) * z)
        + (Complex.exp (-(s + (i : ℂ)) * z) * Rj + Complex.exp (-(s + (j : ℂ)) * z) * Ri)
        + Ri * Rj := by
  rw [← sing_product]; ring

/-- **The N=2 relation collected into the three monodromy blocks.** Writing each `F_k = E_k + R_k` with
`E_k = e^{−(s+k)z}` (singular) and `R_k` (periodic tail), the full degree-≤2 relation
`∑_{i,j} q_{ij} F_iF_j + ∑_k l_k F_k + c` splits exactly into:
* `Φ = ∑_{i,j} q_{ij} E_i E_j` — the doubly-singular **quadratic** block (eigenvalue `e^{−4πis}`),
* `Ψ = ∑_{i,j} q_{ij}(E_i R_j + E_j R_i) + ∑_k l_k E_k` — the singular **linear+cross** block (`e^{−2πis}`),
* `Θ = ∑_{i,j} q_{ij} R_i R_j + ∑_k l_k R_k + c` — the **regular** block (eigenvalue `1`).
Pure algebra (`Fin.sum_univ_three` + `ring`). The `E_iE_j` products become the block exponents
`e^{−(2s+i+j)z}` via `sing_product`, then `quadratic_weight_regroup` collects `A_w = ∑_{i+j=w} q_{ij}`. -/
theorem relation_collect {s : ℂ} (q : Fin 3 → Fin 3 → ℂ) (l : Fin 3 → ℂ) (c : ℂ) (z : ℂ)
    (R : Fin 3 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, q i j *
        ((Complex.exp (-(s + (i : ℂ)) * z) + R i) * (Complex.exp (-(s + (j : ℂ)) * z) + R j)))
      + (∑ k : Fin 3, l k * (Complex.exp (-(s + (k : ℂ)) * z) + R k)) + c
    = (∑ i : Fin 3, ∑ j : Fin 3, q i j *
          (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)))
      + ((∑ i : Fin 3, ∑ j : Fin 3, q i j *
            (Complex.exp (-(s + (i : ℂ)) * z) * R j + Complex.exp (-(s + (j : ℂ)) * z) * R i))
          + ∑ k : Fin 3, l k * Complex.exp (-(s + (k : ℂ)) * z))
      + ((∑ i : Fin 3, ∑ j : Fin 3, q i j * (R i * R j)) + (∑ k : Fin 3, l k * R k) + c) := by
  simp only [Fin.sum_univ_three]
  ring

/-- **The quadratic block in `block_descent` form.** `∑_{i,j} q_{ij} E_i E_j = ∑_{w<5} A_w·e^{−(2s+w)z}`
with `A_w = ∑_{i+j=w} q_{ij}` — `sing_product` turns each `E_iE_j` into the exponent `e^{−(2s+i+j)z}`, and
`quadratic_weight_regroup` collects by weight `w = i+j` (`2N+1 = 5` weights for `N=2`). This is the form
`block_descent` consumes (the coefficient `A_w` is a `ℂ[a]`-polynomial when `q_{ij}` are). -/
theorem phi_block_form {s : ℂ} (q : Fin 3 → Fin 3 → ℂ) (z : ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, q i j *
        (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)))
      = ∑ w ∈ Finset.range 5,
          (∑ ij ∈ Finset.univ.filter
              (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = w), q ij.1 ij.2)
            * Complex.exp (-(2 * s + (w : ℂ)) * z) := by
  have hg : ∀ i j : Fin 3,
      Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)
        = (fun m : ℕ => Complex.exp (-(2 * s + (m : ℂ)) * z)) ((i : ℕ) + (j : ℕ)) := by
    intro i j
    rw [sing_product]
    push_cast
    ring_nf
  simp only [hg]
  exact quadratic_weight_regroup q (fun m : ℕ => Complex.exp (-(2 * s + (m : ℂ)) * z))

/-- **Range-indexed shift-eigenvector** (the `Finset.range` analogue of `block_shift_eigen`, since the
collected blocks are `range`-indexed). A block `∑_{w<K} c_w(·)·e^{β_w·}` with common eigenvalue
`e^{2πiβ_w} = λ` and periodic coefficients is a `λ`-eigenvector of the `2πi`-shift. -/
theorem range_block_eigen {K : ℕ} {β : ℕ → ℂ} {lam : ℂ} {c : ℕ → ℂ → ℂ}
    (hβ : ∀ w, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β w) = lam)
    (hc : ∀ w z, c w (z + 2 * (Real.pi : ℂ) * Complex.I) = c w z) (z : ℂ) :
    (∑ w ∈ Finset.range K, c w (z + 2 * (Real.pi : ℂ) * Complex.I)
        * Complex.exp (β w * (z + 2 * (Real.pi : ℂ) * Complex.I)))
      = lam * ∑ w ∈ Finset.range K, c w z * Complex.exp (β w * z) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hc w z, show β w * (z + 2 * (Real.pi : ℂ) * Complex.I)
        = β w * z + 2 * (Real.pi : ℂ) * Complex.I * β w from by ring, Complex.exp_add, hβ w]
  ring

/-- **The quadratic block is an `e^{−4πis}`-shift-eigenvector.** With `A_w(z) = (filter-sum of
`q_{ij}(−n+e^z)`)` periodic (`e^{z+2πi}=e^z`) and exponents `−(2s+w)` all sharing `e^{2πi(−(2s+w))} =
e^{−4πis}` (integer collapse, `exp_two_pi_I_neg_add_nat` with `a=2s`), the quadratic block scales by
`λ_q = e^{2πi(−2s)}` under the shift — the `hΦ` input of `shift_eigenspace_separation`. -/
theorem phi_block_eigen {s : ℂ} (A : ℕ → ℂ → ℂ)
    (hA : ∀ w z, A w (z + 2 * (Real.pi : ℂ) * Complex.I) = A w z) (z : ℂ) :
    (∑ w ∈ Finset.range 5, A w (z + 2 * (Real.pi : ℂ) * Complex.I)
        * Complex.exp (-(2 * s + (w : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s)))
        * ∑ w ∈ Finset.range 5, A w z * Complex.exp (-(2 * s + (w : ℂ)) * z) :=
  range_block_eigen (β := fun w => -(2 * s + (w : ℂ)))
    (fun w => exp_two_pi_I_neg_add_nat (2 * s) w) hA z

/-- **Singular-exponential shift.** `e^{−(s+k)(z+2πi)} = e^{2πi(−s)}·e^{−(s+k)z}` (the `e^{−2πik}=1`
collapse) — the per-term scaling that makes the linear+cross block an `e^{−2πis}`-eigenvector. -/
theorem Ek_shift {s : ℂ} (k : ℕ) (z : ℂ) :
    Complex.exp (-(s + (k : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) * Complex.exp (-(s + (k : ℂ)) * z) := by
  have hk : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ))) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ))
          = -((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) from by ring,
        Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, inv_one]
  rw [show -(s + (k : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I)
        = -(s + (k : ℂ)) * z + 2 * (Real.pi : ℂ) * Complex.I * (-s)
          + 2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ)) from by ring,
      Complex.exp_add, Complex.exp_add, hk, mul_one]
  ring

/-- **The regular block is shift-invariant (eigenvalue `1`).** Every component (`q_{ij}`, `l_k`, `c`,
`R_k`) is `2πi`-periodic, so `Θ(z+2πi) = Θ(z)` — the `hΘ` input of `shift_eigenspace_separation`. -/
theorem theta_block_eigen {q : Fin 3 → Fin 3 → ℂ → ℂ} {l : Fin 3 → ℂ → ℂ} {cc : ℂ → ℂ}
    {R : Fin 3 → ℂ → ℂ}
    (hq : ∀ i j z, q i j (z + 2 * (Real.pi : ℂ) * Complex.I) = q i j z)
    (hl : ∀ k z, l k (z + 2 * (Real.pi : ℂ) * Complex.I) = l k z)
    (hcc : ∀ z, cc (z + 2 * (Real.pi : ℂ) * Complex.I) = cc z)
    (hR : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z) (z : ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, q i j (z + 2 * (Real.pi : ℂ) * Complex.I)
        * (R i (z + 2 * (Real.pi : ℂ) * Complex.I) * R j (z + 2 * (Real.pi : ℂ) * Complex.I)))
      + (∑ k : Fin 3, l k (z + 2 * (Real.pi : ℂ) * Complex.I)
          * R k (z + 2 * (Real.pi : ℂ) * Complex.I)) + cc (z + 2 * (Real.pi : ℂ) * Complex.I)
    = (∑ i : Fin 3, ∑ j : Fin 3, q i j z * (R i z * R j z))
      + (∑ k : Fin 3, l k z * R k z) + cc z := by
  simp only [hq, hl, hcc, hR]

/-- **The linear+cross block is an `e^{−2πis}`-shift-eigenvector.** Each term carries exactly one
singular exponential `E_k` (scaling by `e^{2πi(−s)}` via `Ek_shift`) times `2πi`-periodic factors, so
`Ψ(z+2πi) = e^{2πi(−s)}·Ψ(z)` — the `hΨ` input of `shift_eigenspace_separation`. -/
theorem psi_block_eigen {s : ℂ} {q : Fin 3 → Fin 3 → ℂ → ℂ} {l : Fin 3 → ℂ → ℂ}
    {R : Fin 3 → ℂ → ℂ}
    (hq : ∀ i j z, q i j (z + 2 * (Real.pi : ℂ) * Complex.I) = q i j z)
    (hl : ∀ k z, l k (z + 2 * (Real.pi : ℂ) * Complex.I) = l k z)
    (hR : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z) (z : ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, q i j (z + 2 * (Real.pi : ℂ) * Complex.I)
        * (Complex.exp (-(s + (i : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
            * R j (z + 2 * (Real.pi : ℂ) * Complex.I)
          + Complex.exp (-(s + (j : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
            * R i (z + 2 * (Real.pi : ℂ) * Complex.I)))
      + ∑ k : Fin 3, l k (z + 2 * (Real.pi : ℂ) * Complex.I)
          * Complex.exp (-(s + (k : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
    = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s))
      * ((∑ i : Fin 3, ∑ j : Fin 3, q i j z
            * (Complex.exp (-(s + (i : ℂ)) * z) * R j z + Complex.exp (-(s + (j : ℂ)) * z) * R i z))
        + ∑ k : Fin 3, l k z * Complex.exp (-(s + (k : ℂ)) * z)) := by
  simp only [hq, hl, hR, Ek_shift]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-- `e^{2πi·w} ≠ 1` when `w ∉ ℤ`. -/
theorem exp_two_pi_I_ne_one {w : ℂ} (hw : ∀ n : ℤ, (n : ℂ) ≠ w) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) ≠ 1 := by
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  apply hw n
  have hpiI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcancel : (2 * (Real.pi : ℂ) * Complex.I) * w = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    linear_combination hn
  exact (mul_left_cancel₀ hpiI hcancel).symm

/-- `λ_l = e^{2πi(−s)} ≠ 1` (`s ∉ ℤ`). -/
theorem ll_ne_one {s : ℂ} (hs : ∀ n : ℤ, (n : ℂ) ≠ s) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) ≠ 1 :=
  exp_two_pi_I_ne_one (fun n h => hs (-n) (by push_cast at h ⊢; linear_combination -h))

/-- `λ_q = e^{2πi(−2s)} ≠ 1` (`2s ∉ ℤ`). -/
theorem lq_ne_one {s : ℂ} (h2s : ∀ n : ℤ, (n : ℂ) ≠ 2 * s) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))) ≠ 1 :=
  exp_two_pi_I_ne_one (fun n h => h2s (-n) (by push_cast at h ⊢; linear_combination -h))

/-- `λ_q ≠ λ_l` (`s ∉ ℤ`). -/
theorem lq_ne_ll {s : ℂ} (hs : ∀ n : ℤ, (n : ℂ) ≠ s) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s)))
      ≠ Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) := by
  intro hcon
  apply ll_ne_one hs
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s)))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * s)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * s) := by rw [hcon]
  rw [← Complex.exp_add, ← Complex.exp_add,
      show 2 * (Real.pi : ℂ) * Complex.I * (-(2 * s)) + 2 * (Real.pi : ℂ) * Complex.I * s
        = 2 * (Real.pi : ℂ) * Complex.I * (-s) from by ring,
      show 2 * (Real.pi : ℂ) * Complex.I * (-s) + 2 * (Real.pi : ℂ) * Complex.I * s
        = 0 from by ring, Complex.exp_zero] at h2
  exact h2

/-- **N=2 separation milestone.** With `s ∉ ℤ` and `2s ∉ ℤ` the three monodromy eigenvalues
`λ_q = e^{2πi(−2s)}`, `λ_l = e^{2πi(−s)}`, `1` are distinct, so a relation `Φ + Ψ + Θ = 0` on a
`2πi`-invariant region whose blocks are the respective shift-eigenvectors forces each block to vanish
separately (`shift_eigenspace_separation`). -/
theorem n2_separation {s : ℂ} (hs : ∀ n : ℤ, (n : ℂ) ≠ s) (h2s : ∀ n : ℤ, (n : ℂ) ≠ 2 * s)
    {Φ Ψ Θ : ℂ → ℂ} {U : Set ℂ} (hUinv : ∀ z ∈ U, z + 2 * (Real.pi : ℂ) * Complex.I ∈ U)
    (hΦ : ∀ z ∈ U, Φ (z + 2 * (Real.pi : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))) * Φ z)
    (hΨ : ∀ z ∈ U, Ψ (z + 2 * (Real.pi : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) * Ψ z)
    (hΘ : ∀ z ∈ U, Θ (z + 2 * (Real.pi : ℂ) * Complex.I) = Θ z)
    (hrel : ∀ z ∈ U, Φ z + Ψ z + Θ z = 0) :
    ∀ z ∈ U, Φ z = 0 ∧ Ψ z = 0 ∧ Θ z = 0 :=
  shift_eigenspace_separation hUinv hΦ hΨ hΘ (lq_ne_ll hs) (lq_ne_one h2s) (ll_ne_one hs) hrel

/-- The weight-`w` filter over `Fin 3 × Fin 3` (the pairs `(i,j)` with `i+j = w`), evaluated by `decide`:
`w=0 → {(0,0)}`, `w=2 → {(0,2),(1,1),(2,0)}`, `w=4 → {(2,2)}`, etc. These turn `A_w = ∑_{i+j=w} q_{ij} = 0`
into the triangular system on the coefficients. -/
theorem weight_filter_eval (q : Fin 3 → Fin 3 → Polynomial ℂ) :
    (∑ ij ∈ Finset.univ.filter
        (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 0), q ij.1 ij.2) = q 0 0
    ∧ (∑ ij ∈ Finset.univ.filter
        (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 4), q ij.1 ij.2) = q 2 2
    ∧ (∑ ij ∈ Finset.univ.filter
        (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 2), q ij.1 ij.2)
        = q 0 2 + q 1 1 + q 2 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (Finset.univ.filter (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 0))
        = {(0, 0)} from by decide, Finset.sum_singleton]
  · rw [show (Finset.univ.filter (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 4))
        = {(2, 2)} from by decide, Finset.sum_singleton]
  · rw [show (Finset.univ.filter (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 2))
        = {(0, 2), (1, 1), (2, 0)} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring

/-- The left half-plane `{Re z < B}` is closed under the `2πi`-shift (`Re(z+2πi) = Re z`) — the
`2πi`-invariant region `n2_separation`/`shift_eigenspace_separation` run on. -/
theorem halfplane_invariant {B : ℝ} {z : ℂ} (hz : z.re < B) :
    (z + 2 * (Real.pi : ℂ) * Complex.I).re < B := by
  have h0 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  rw [Complex.add_re, h0, add_zero]; exact hz

/-- A coefficient `z ↦ p(−n+e^z)` is `2πi`-periodic (`e^{z+2πi}=e^z`) — supplies the `hc`/`hA`
periodicity inputs of the block eigenvector lemmas, for `p` a `ℂ[a]`-coefficient or a Hurwitz tail. -/
theorem coeff_periodic (p : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    p.eval (-(n : ℂ) + Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I))
      = p.eval (-(n : ℂ) + Complex.exp z) := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Strip → half-plane continuation.** The split `F_k = E_k + R_k` (`Fk_zform`) holds only on the strip
`Im z ∈ (−π,π)`, which is *not* `2πi`-invariant; but the collected relation `g = Φ+Ψ+Θ` is analytic on
the half-plane `{Re z < B}` and vanishes on the open strip-slice, so by the identity theorem it vanishes
on the whole (connected) half-plane — the `2πi`-invariant region `n2_separation` needs. -/
theorem split_extend {g : ℂ → ℂ} {B : ℝ}
    (hg : AnalyticOnNhd ℂ g {z : ℂ | z.re < B})
    (hstrip : ∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi → g z = 0)
    {z0 : ℂ} (h0re : z0.re < B) (h0im1 : -Real.pi < z0.im) (h0im2 : z0.im < Real.pi)
    {z : ℂ} (hz : z.re < B) : g z = 0 := by
  have hpre : IsPreconnected {z : ℂ | z.re < B} :=
    ((convex_Iio B).linear_preimage Complex.reLm).isPreconnected
  have hopen : IsOpen {w : ℂ | w.re < B ∧ -Real.pi < w.im ∧ w.im < Real.pi} := by
    have h1 : IsOpen {w : ℂ | w.re < B} := isOpen_lt Complex.continuous_re continuous_const
    have h2 : IsOpen {w : ℂ | -Real.pi < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have h3 : IsOpen {w : ℂ | w.im < Real.pi} := isOpen_lt Complex.continuous_im continuous_const
    exact h1.inter (h2.inter h3)
  have hfreq : ∃ᶠ w in nhdsWithin z0 {z0}ᶜ, g w = 0 := by
    have hev : ∀ᶠ w in nhds z0, g w = 0 := by
      filter_upwards [hopen.mem_nhds ⟨h0re, h0im1, h0im2⟩] with w hw
      exact hstrip w hw.1 hw.2.1 hw.2.2
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre h0re hfreq hz

end HurwitzEncoding
