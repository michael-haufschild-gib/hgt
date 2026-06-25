/-
# Hurwitz all-N — the quadratic-block convolution regroup

The all-`N` quadratic filtration upgrades the proven `N=2` quadratic descent to every finite shift
ladder `{ζ(s+k,a)}_{0≤k≤N}`. The descent engine (`HurwitzSpine.block_descent`) is already generic in
the block width `W`; the only `N`-specific ingredient is the **convolution regroup** that turns the
doubly-singular product block `∑_{i,j} q_{ij}·E_iE_j` (`E_k = e^{−(s+k)z}`) into the weight form
`∑_w A_w·e^{−(2s+w)z}` with `A_w = ∑_{i+j=w} q_{ij}` — the form `block_descent` consumes. This is the
general-`N` analogue of `HurwitzEncoding.phi_block_form` (which is hard-wired to `Fin 3`).
-/
import GaloisForLFunctions.Hurwitz.Spine
import GaloisForLFunctions.Hurwitz.Encoding
import GaloisForLFunctions.Hurwitz.N2BlockAnalytic

open Complex HurwitzEncoding HurwitzN2Tail HurwitzN2BlockAnalytic

namespace HurwitzAllNQuadFilt

variable {N : ℕ}

/-- The weight-`w` quadratic coefficient over the full `(N+1)`-ladder: `A_w = ∑_{i+j=w} q_{ij}`. -/
noncomputable def AqN (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (w : ℕ) : Polynomial ℂ :=
  ∑ ij ∈ Finset.univ.filter (fun ij : Fin (N + 1) × Fin (N + 1) => (ij.1 : ℕ) + (ij.2 : ℕ) = w),
    q ij.1 ij.2

/-- **The quadratic block, product form = weight form.** With `E_k = e^{−(s+k)z}`,
`∑_{i,j} q_{ij}·E_iE_j = ∑_{w≤2N} (∑_{i+j=w} q_{ij})·e^{−(2s+w)z}` — group the product double-sum by the
total weight `i+j`, on whose fiber the common exponential `e^{−(2s+(i+j))z}` is constant. -/
theorem phiN_regroup (s : ℂ) (q : Fin (N + 1) → Fin (N + 1) → ℂ) (z : ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        q i j * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)))
      = ∑ w ∈ Finset.range (2 * N + 1),
        (∑ ij ∈ Finset.univ.filter
          (fun ij : Fin (N + 1) × Fin (N + 1) => (ij.1 : ℕ) + (ij.2 : ℕ) = w), q ij.1 ij.2)
        * Complex.exp (-(2 * s + (w : ℂ)) * z) := by
  have hcomb : ∀ i j : Fin (N + 1),
      q i j * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z))
        = q i j * Complex.exp (-(2 * s + (((i : ℕ) + (j : ℕ) : ℕ) : ℂ)) * z) := by
    intro i j
    rw [← Complex.exp_add]; congr 2; push_cast; ring
  simp_rw [hcomb]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1)))) (t := Finset.range (2 * N + 1))
    (g := fun ij : Fin (N + 1) × Fin (N + 1) => (ij.1 : ℕ) + (ij.2 : ℕ))
    (fun ij _ => by
      simp only [Finset.mem_range]
      have h1 : (ij.1 : ℕ) ≤ N := Nat.lt_succ_iff.mp ij.1.isLt
      have h2 : (ij.2 : ℕ) ≤ N := Nat.lt_succ_iff.mp ij.2.isLt
      omega)
    (fun ij => q ij.1 ij.2 * Complex.exp (-(2 * s + (((ij.1 : ℕ) + (ij.2 : ℕ) : ℕ) : ℂ)) * z))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  have hw : (ij.1 : ℕ) + (ij.2 : ℕ) = w := (Finset.mem_filter.mp hij).2
  rw [hw]

/-- **All-`N` quadratic-block descent.** Vanishing of the doubly-singular quadratic block
`∑_{w≤2N} A_w(−n+e^z)·e^{−(2s+w)z}` (for every large `n`, on the deep half-plane) forces every weight
coefficient `A_w = ∑_{i+j=w} q_{ij} = 0`. This is `HurwitzSpine.block_descent` at width `W = 2N` — the
descent engine is width-generic, so the upgrade from `N=2` to every finite ladder is immediate once the
product block is put in weight form by `phiN_regroup`. -/
theorem allN_quad_descent {s : ℂ} (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) {M : ℕ}
    {Bregion : ℕ → ℝ}
    (hΦ : ∀ n, M ≤ n → ∀ z : ℂ, z.re < Bregion n →
      ∑ w ∈ Finset.range (2 * N + 1), (AqN q w).eval (-(n : ℂ) + Complex.exp z)
        * Complex.exp (-(2 * s + (w : ℂ)) * z) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 :=
  HurwitzSpine.block_descent (s := s) (A := AqN q) (W := 2 * N) (N := M) (Bregion := Bregion) hΦ

/-- **All-`N` quadratic filtration (product-form input).** If the genuine doubly-singular product block
`∑_{i,j} q_{ij}(−n+e^z)·E_iE_j` (`E_k = e^{−(s+k)z}`) vanishes on the deep half-plane for every large
`n`, then every weight coefficient `A_w = ∑_{i+j=w} q_{ij}` vanishes. Combines `phiN_regroup` (product →
weight) with `allN_quad_descent`. -/
theorem allN_quad_filtration {s : ℂ} (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) {M : ℕ}
    {Bregion : ℕ → ℝ}
    (hΦ : ∀ n, M ≤ n → ∀ z : ℂ, z.re < Bregion n →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
        * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z))) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 := by
  apply allN_quad_descent (s := s) q (M := M) (Bregion := Bregion)
  intro n hn z hz
  have hev : ∀ w, (AqN q w).eval (-(n : ℂ) + Complex.exp z)
      = ∑ ij ∈ Finset.univ.filter
          (fun ij : Fin (N + 1) × Fin (N + 1) => (ij.1 : ℕ) + (ij.2 : ℕ) = w),
        (q ij.1 ij.2).eval (-(n : ℂ) + Complex.exp z) := by
    intro w; rw [AqN, Polynomial.eval_finsetSum]
  simp_rw [hev]
  rw [← phiN_regroup s (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z)) z]
  exact hΦ n hn z hz

/-! ## The general-`N` monodromy separation (relation ⟹ quadratic block vanishes) -/

/-- The doubly-singular **quadratic** block over the full `(N+1)`-ladder (product form). -/
noncomputable def PhiN (s : ℂ) (n : ℕ) (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
    * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z))

/-- The singular **linear+cross** block over the full `(N+1)`-ladder. -/
noncomputable def PsiN (s : ℂ) (n : ℕ) (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (R : Fin (N + 1) → ℂ → ℂ) (z : ℂ) : ℂ :=
  (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
      * (Complex.exp (-(s + (i : ℂ)) * z) * R j z + Complex.exp (-(s + (j : ℂ)) * z) * R i z))
    + ∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z) * Complex.exp (-(s + (k : ℂ)) * z)

/-- The **regular** block over the full `(N+1)`-ladder. -/
noncomputable def ThetaN (s : ℂ) (n : ℕ) (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (R : Fin (N + 1) → ℂ → ℂ) (z : ℂ) : ℂ :=
  (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z) * (R i z * R j z))
    + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z) * R k z)
    + cc.eval (-(n : ℂ) + Complex.exp z)

/-- **The degree-≤2 relation collected into the three monodromy blocks (general `N`).** Writing each
`F_k = E_k + R_k`, the relation `∑_{i,j} q_{ij}F_iF_j + ∑_k l_k F_k + c` splits into the doubly-singular
quadratic block, the singular linear+cross block, and the regular block — the `Fin (N+1)` analogue of
`HurwitzEncoding.relation_collect`, proved by splitting the sums rather than `Fin.sum_univ_three`. -/
theorem relation_collectN {s : ℂ} (q : Fin (N + 1) → Fin (N + 1) → ℂ) (l : Fin (N + 1) → ℂ) (c : ℂ)
    (z : ℂ) (R : Fin (N + 1) → ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j
        * ((Complex.exp (-(s + (i : ℂ)) * z) + R i) * (Complex.exp (-(s + (j : ℂ)) * z) + R j)))
      + (∑ k : Fin (N + 1), l k * (Complex.exp (-(s + (k : ℂ)) * z) + R k)) + c
    = (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j
          * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)))
      + ((∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j
            * (Complex.exp (-(s + (i : ℂ)) * z) * R j + Complex.exp (-(s + (j : ℂ)) * z) * R i))
          + ∑ k : Fin (N + 1), l k * Complex.exp (-(s + (k : ℂ)) * z))
      + ((∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (R i * R j))
          + (∑ k : Fin (N + 1), l k * R k) + c) := by
  have hq3 : (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j
        * ((Complex.exp (-(s + (i : ℂ)) * z) + R i) * (Complex.exp (-(s + (j : ℂ)) * z) + R j)))
      = (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j
            * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)))
        + (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j
            * (Complex.exp (-(s + (i : ℂ)) * z) * R j + Complex.exp (-(s + (j : ℂ)) * z) * R i))
        + (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (R i * R j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hl2 : (∑ k : Fin (N + 1), l k * (Complex.exp (-(s + (k : ℂ)) * z) + R k))
      = (∑ k : Fin (N + 1), l k * Complex.exp (-(s + (k : ℂ)) * z))
        + (∑ k : Fin (N + 1), l k * R k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hq3, hl2]; ring

/-- **The quadratic block is an `e^{−4πis}`-shift-eigenvector (general `N`).** Each `E_iE_j` scales by
`e^{−2πis}·e^{−2πis} = e^{−4πis}` (`Ek_shift` twice), the coefficients are periodic. -/
theorem phiN_block_eigen {s : ℂ} {Q : Fin (N + 1) → Fin (N + 1) → ℂ → ℂ}
    (hQ : ∀ i j z, Q i j (z + 2 * (Real.pi : ℂ) * Complex.I) = Q i j z) (z : ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Q i j (z + 2 * (Real.pi : ℂ) * Complex.I)
        * (Complex.exp (-(s + (i : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
          * Complex.exp (-(s + (j : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s)))
        * ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Q i j z
          * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)) := by
  have hlam : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [hQ, Ek_shift]
  rw [hlam, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **The linear+cross block is an `e^{−2πis}`-shift-eigenvector (general `N`).** -/
theorem psiN_block_eigen {s : ℂ} {q : Fin (N + 1) → Fin (N + 1) → ℂ → ℂ} {l : Fin (N + 1) → ℂ → ℂ}
    {R : Fin (N + 1) → ℂ → ℂ}
    (hq : ∀ i j z, q i j (z + 2 * (Real.pi : ℂ) * Complex.I) = q i j z)
    (hl : ∀ k z, l k (z + 2 * (Real.pi : ℂ) * Complex.I) = l k z)
    (hR : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z) (z : ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j (z + 2 * (Real.pi : ℂ) * Complex.I)
        * (Complex.exp (-(s + (i : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
            * R j (z + 2 * (Real.pi : ℂ) * Complex.I)
          + Complex.exp (-(s + (j : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
            * R i (z + 2 * (Real.pi : ℂ) * Complex.I)))
      + ∑ k : Fin (N + 1), l k (z + 2 * (Real.pi : ℂ) * Complex.I)
          * Complex.exp (-(s + (k : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I))
    = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s))
      * ((∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j z
            * (Complex.exp (-(s + (i : ℂ)) * z) * R j z + Complex.exp (-(s + (j : ℂ)) * z) * R i z))
        + ∑ k : Fin (N + 1), l k z * Complex.exp (-(s + (k : ℂ)) * z)) := by
  simp only [hq, hl, hR, Ek_shift]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **The regular block is shift-invariant (general `N`).** -/
theorem thetaN_block_eigen {q : Fin (N + 1) → Fin (N + 1) → ℂ → ℂ} {l : Fin (N + 1) → ℂ → ℂ}
    {cc : ℂ → ℂ} {R : Fin (N + 1) → ℂ → ℂ}
    (hq : ∀ i j z, q i j (z + 2 * (Real.pi : ℂ) * Complex.I) = q i j z)
    (hl : ∀ k z, l k (z + 2 * (Real.pi : ℂ) * Complex.I) = l k z)
    (hcc : ∀ z, cc (z + 2 * (Real.pi : ℂ) * Complex.I) = cc z)
    (hR : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z) (z : ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j (z + 2 * (Real.pi : ℂ) * Complex.I)
        * (R i (z + 2 * (Real.pi : ℂ) * Complex.I) * R j (z + 2 * (Real.pi : ℂ) * Complex.I)))
      + (∑ k : Fin (N + 1), l k (z + 2 * (Real.pi : ℂ) * Complex.I)
          * R k (z + 2 * (Real.pi : ℂ) * Complex.I)) + cc (z + 2 * (Real.pi : ℂ) * Complex.I)
    = (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j z * (R i z * R j z))
      + (∑ k : Fin (N + 1), l k z * R k z) + cc z := by
  simp only [hq, hl, hcc, hR]

/-- **General-`N` separation (assembled).** Given the block sum is analytic on `{Re z < B}` and vanishes
on the open strip-slice, each monodromy block vanishes on the whole half-plane (`s,2s ∉ ℤ`). The
`Fin (N+1)` analogue of `HurwitzN2Main.n2_blocks_vanish`. -/
theorem allN_blocks_vanish {s : ℂ} (n : ℕ) (hs : ∀ k : ℤ, (k : ℂ) ≠ s) (h2s : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (R : Fin (N + 1) → ℂ → ℂ)
    (hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z)
    {B : ℝ} {z0 : ℂ} (h0re : z0.re < B) (h0im1 : -Real.pi < z0.im) (h0im2 : z0.im < Real.pi)
    (hanalytic : AnalyticOnNhd ℂ
      (fun z => PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z) {z : ℂ | z.re < B})
    (hrel_split : ∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi →
      PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0) :
    (∀ z : ℂ, z.re < B → PhiN s n q z = 0) ∧ (∀ z : ℂ, z.re < B → PsiN s n q l R z = 0)
      ∧ (∀ z : ℂ, z.re < B → ThetaN s n q l cc R z = 0) := by
  have hg0 : ∀ z : ℂ, z.re < B → PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0 :=
    fun z hz => split_extend hanalytic hrel_split h0re h0im1 h0im2 hz
  have hΦ : ∀ z ∈ {z : ℂ | z.re < B}, PhiN s n q (z + 2 * (Real.pi : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))) * PhiN s n q z := fun z _ =>
    phiN_block_eigen (Q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (fun i j z => coeff_periodic (q i j) n z) z
  have hΨ : ∀ z ∈ {z : ℂ | z.re < B}, PsiN s n q l R (z + 2 * (Real.pi : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) * PsiN s n q l R z := fun z _ =>
    psiN_block_eigen (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z) hRper z
  have hΘ : ∀ z ∈ {z : ℂ | z.re < B}, ThetaN s n q l cc R (z + 2 * (Real.pi : ℂ) * Complex.I)
      = ThetaN s n q l cc R z := fun z _ =>
    thetaN_block_eigen (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z))
      (cc := fun z => cc.eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z)
      (fun z => coeff_periodic cc n z) hRper z
  have hsep := n2_separation hs h2s
    (fun z (hz : z.re < B) => halfplane_invariant (B := B) (z := z) hz) hΦ hΨ hΘ
    (fun z hz => hg0 z hz)
  exact ⟨fun z hz => (hsep z hz).1, fun z hz => (hsep z hz).2.1, fun z hz => (hsep z hz).2.2⟩

/-- **All-`N` quadratic vanishing from the genuine relation.** If the genuine factored degree-≤2 relation
among `{ζ(s+k,−n+e^z)}_{k≤N}` holds on the strip for every large `n`, and the block sum is analytic on
the deep half-plane, then every weight coefficient `A_w = ∑_{i+j=w} q_{ij} = 0`. Combines
`relation_collectN` (regroup), `allN_blocks_vanish` (separation) and `allN_quad_filtration` (descent). -/
theorem allN_quad_vanish {s : ℂ} (hs : ∀ k : ℤ, (k : ℂ) ≠ s) (h2s : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    {M : ℕ} (R : ℕ → Fin (N + 1) → ℂ → ℂ)
    (hRper : ∀ n k z, R n k (z + 2 * (Real.pi : ℂ) * Complex.I) = R n k z)
    (hanalytic : ∀ n, M ≤ n → AnalyticOnNhd ℂ
      (fun z => PhiN s n q z + PsiN s n q l (R n) z + ThetaN s n q l cc (R n) z)
      {z : ℂ | z.re < -Real.log 2})
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + R n i z)
            * (Complex.exp (-(s + (j : ℂ)) * z) + R n j z)))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + R n k z))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 := by
  have hlog : -1 < -Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  apply allN_quad_filtration (s := s) q (M := M) (Bregion := fun _ => -Real.log 2)
  intro n hn z hz
  have hsplit : ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      PhiN s n q z + PsiN s n q l (R n) z + ThetaN s n q l cc (R n) z = 0 := by
    intro z hz1 hz2 hz3
    rw [PhiN, PsiN, ThetaN]
    have hcoll := relation_collectN (s := s) (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (fun k => (l k).eval (-(n : ℂ) + Complex.exp z)) (cc.eval (-(n : ℂ) + Complex.exp z)) z
      (fun k => R n k z)
    have hr := hrel n hn z hz1 hz2 hz3
    linear_combination hr - hcoll
  exact (allN_blocks_vanish n hs h2s q l cc (R n) (hRper n) (z0 := -1) (B := -Real.log 2)
    (by simpa using hlog) (by simpa using hpi) (by simpa using hpi) (hanalytic n hn) hsplit).1 z hz

/-- **The general-`N` block sum is analytic on the deep half-plane (discharges the analyticity input).**
With the factored tail `R_k z = tailFactored s k n (e^z)` analytic on `{‖x‖<1/2}`
(`N2TailAnalytic.tailFactored_analytic`), the blocks `PhiN, PsiN, ThetaN` are built from entire pieces
(`e^{c·z}`, `p(−n+e^z)`) and that analytic tail, so their sum is analytic on `{Re z < −log 2}`. The
`Fin (N+1)` analogue of `HurwitzN2BlockAnalytic.blockSum_analytic`. -/
theorem allN_blockSum_analytic {s : ℂ} (hs : 1 < s.re) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z => PhiN s n q z
      + PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z
      + ThetaN s n q l cc (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z)
      {z : ℂ | z.re < -Real.log 2} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt Complex.continuous_re continuous_const)
  have htail : ∀ k : Fin (N + 1),
      DifferentiableOn ℂ (fun z => tailFactored s (k : ℕ) n (Complex.exp z))
        {z : ℂ | z.re < -Real.log 2} :=
    fun k => (tailFactored_analytic hs (k : ℕ) n).differentiableOn.comp
      Complex.differentiable_exp.differentiableOn exp_mapsTo
  have hpoly : ∀ p : Polynomial ℂ,
      DifferentiableOn ℂ (fun z => p.eval (-(n : ℂ) + Complex.exp z)) {z : ℂ | z.re < -Real.log 2} := by
    intro p; fun_prop
  have hexp : ∀ c : ℂ,
      DifferentiableOn ℂ (fun z => Complex.exp (c * z)) {z : ℂ | z.re < -Real.log 2} := by
    intro c; fun_prop
  unfold PhiN PsiN ThetaN
  refine ((DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
      (hpoly _).mul ((hexp _).mul (hexp _))).add
    ((DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (hpoly _).mul (((hexp _).mul (htail j)).add ((hexp _).mul (htail i)))).add
      (DifferentiableOn.fun_sum fun k _ => (hpoly _).mul (hexp _)))).add
    (((DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (hpoly _).mul ((htail i).mul (htail j))).add
      (DifferentiableOn.fun_sum fun k _ => (hpoly _).mul (htail k))).add (hpoly cc))

/-- **All-`N` quadratic filtration — UNCONDITIONAL (analyticity discharged).** From the genuine factored
degree-≤2 relation among `{ζ(s+k,−n+e^z)}_{k≤N}` (with `R = tailFactored`, the analytic local tails) on
the strip for every large `n`, every weight coefficient `A_w = ∑_{i+j=w} q_{ij}` vanishes — no separate
analyticity hypothesis, discharged by `allN_blockSum_analytic`. -/
theorem allN_quad_vanish_genuine {s : ℂ} (hs1 : 1 < s.re) (hs : ∀ k : ℤ, (k : ℂ) ≠ s)
    (h2s : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 :=
  allN_quad_vanish hs h2s q l cc (R := fun n k z => tailFactored s (k : ℕ) n (Complex.exp z))
    (fun n k z => tailFactored_periodic s (k : ℕ) n z)
    (fun n _ => allN_blockSum_analytic hs1 n q l cc) hrel

end HurwitzAllNQuadFilt

