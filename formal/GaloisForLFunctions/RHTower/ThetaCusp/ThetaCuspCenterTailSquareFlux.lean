import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailSeamGram
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourSeamSplit

/-!
# The native fibre form is a square plus a null Lagrangian

At every center `y` the native signed fibre form of every finite section splits as

`Σ_{i,j} v_i v_j h_{i+j}(y) = |G_v(y)|² + B_v'(y)`,  `G_v = Σ_j v_j (2i)^j Φ^{(j)}`,

with an explicit flux `B_v`, a finite combination of products `Φ^{(a)} Φ^{(b)}`. Mechanism: by
Leibniz `h_{2n} = (−1)^n Σ_m C(2n,m)(−1)^m φ_m φ_{2n−m}`, and every product `φ_a φ_{2n−a}` equals
`(−1)^{n−a} φ_n²` up to the derivative of an alternating telescoping sum; both the Hankel entry
and the Gram entry reduce to `4^n φ_n²`. Integrating beyond the center, the tail form at
`x = r/2` is the bulk `L²` mass of `G_v` beyond `x` minus the local flux:

`Σ_{i,j} v_i v_j U_{i+j}(r) = 2∫_{y>x} |G_v|² − 2B_v(x)`.

At the seam (`x = 0`) the flux vanishes by symmetry and this is the Plancherel Gram law.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

private theorem hasDerivAt_pairProduct (p q : ℕ) (y : ℝ) :
    HasDerivAt (fun y => iteratedDeriv p thetaCuspFullSource y * iteratedDeriv q thetaCuspFullSource y)
      (iteratedDeriv (p+1) thetaCuspFullSource y * iteratedDeriv q thetaCuspFullSource y +
        iteratedDeriv p thetaCuspFullSource y * iteratedDeriv (q+1) thetaCuspFullSource y) y :=
  (hasDerivAt_iteratedDeriv_thetaCuspFullSource p y).mul
    (hasDerivAt_iteratedDeriv_thetaCuspFullSource q y)

/-- The telescoping flux `Σ_{l<n−a} (−1)^l φ_{a+l} φ_{2n−1−a−l}`, carrying `φ_a φ_{2n−a}` to
`(−1)^{n−a} φ_n²`. -/
def thetaCuspPairFlux (n a : ℕ) (y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (n - a), (-1:ℝ)^l *
    (iteratedDeriv (a+l) thetaCuspFullSource y * iteratedDeriv (2*n-1-a-l) thetaCuspFullSource y)

theorem thetaCuspPairFlux_eq_sub {n a : ℕ} (h : a < n) (y : ℝ) :
    thetaCuspPairFlux n a y = iteratedDeriv a thetaCuspFullSource y *
      iteratedDeriv (2*n-1-a) thetaCuspFullSource y - thetaCuspPairFlux n (a+1) y := by
  unfold thetaCuspPairFlux
  rw [show n - a = (n - (a+1)) + 1 by omega, Finset.sum_range_succ']
  have hterm : ∀ l ∈ Finset.range (n-(a+1)), (-1:ℝ)^(l+1) *
      (iteratedDeriv (a+(l+1)) thetaCuspFullSource y *
        iteratedDeriv (2*n-1-a-(l+1)) thetaCuspFullSource y) =
      -((-1:ℝ)^l * (iteratedDeriv (a+1+l) thetaCuspFullSource y *
        iteratedDeriv (2*n-1-(a+1)-l) thetaCuspFullSource y)) := by
    intro l _
    rw [show a+(l+1) = a+1+l by omega, show 2*n-1-a-(l+1) = 2*n-1-(a+1)-l by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  simp only [pow_zero, one_mul, add_zero, Nat.sub_zero]
  ring

/-- **Telescoping flux.** For `a + d = n`,
`(Σ_{l<d} (−1)^l φ_{a+l} φ_{2n−1−a−l})' = φ_a φ_{2n−a} − (−1)^d φ_n²`. -/
theorem hasDerivAt_thetaCuspPairFlux (n : ℕ) : ∀ d a : ℕ, a + d = n → ∀ y : ℝ,
    HasDerivAt (thetaCuspPairFlux n a)
      (iteratedDeriv a thetaCuspFullSource y * iteratedDeriv (2*n-a) thetaCuspFullSource y -
        (-1:ℝ)^d * (iteratedDeriv n thetaCuspFullSource y * iteratedDeriv n thetaCuspFullSource y))
      y := by
  intro d
  induction d with
  | zero =>
    intro a ha y
    obtain rfl : n = a := by omega
    have h0 : thetaCuspPairFlux n n = fun _ => 0 := by
      funext y; simp [thetaCuspPairFlux]
    rw [h0, show 2*n-n = n by omega, pow_zero, one_mul, sub_self]
    exact hasDerivAt_const y 0
  | succ d ih =>
    intro a ha y
    have hrec : thetaCuspPairFlux n a = fun y => iteratedDeriv a thetaCuspFullSource y *
        iteratedDeriv (2*n-1-a) thetaCuspFullSource y - thetaCuspPairFlux n (a+1) y := by
      funext y; exact thetaCuspPairFlux_eq_sub (by omega) y
    rw [hrec]
    have h1 := hasDerivAt_pairProduct a (2*n-1-a) y
    have h2 := ih (a+1) (by omega) y
    refine (h1.sub h2).congr_deriv ?_
    rw [show 2*n-1-a+1 = 2*n-a by omega, show 2*n-(a+1) = 2*n-1-a by omega, pow_succ]
    ring

/-- The flux of the product `φ_m φ_{2n−m}` for any `m ≤ 2n`, using the symmetry `m ↔ 2n − m`. -/
def thetaCuspSymFlux (n m : ℕ) : ℝ → ℝ :=
  if m ≤ n then thetaCuspPairFlux n m else thetaCuspPairFlux n (2*n-m)

theorem hasDerivAt_thetaCuspSymFlux {n m : ℕ} (hm : m ≤ 2*n) (y : ℝ) :
    HasDerivAt (thetaCuspSymFlux n m)
      (iteratedDeriv m thetaCuspFullSource y * iteratedDeriv (2*n-m) thetaCuspFullSource y -
        (-1:ℝ)^(n+m) * (iteratedDeriv n thetaCuspFullSource y *
          iteratedDeriv n thetaCuspFullSource y)) y := by
  unfold thetaCuspSymFlux
  split_ifs with h
  · refine (hasDerivAt_thetaCuspPairFlux n (n-m) m (by omega) y).congr_deriv ?_
    rw [show n+m = (n-m) + 2*m by omega, pow_add, pow_mul]
    norm_num
  · refine (hasDerivAt_thetaCuspPairFlux n (m-n) (2*n-m) (by omega) y).congr_deriv ?_
    rw [show 2*n-(2*n-m) = m by omega, show n+m = (m-n) + 2*n by omega, pow_add, pow_mul]
    norm_num
    ring

theorem integrable_thetaCuspPairFlux (n a : ℕ) : Integrable (thetaCuspPairFlux n a) := by
  unfold thetaCuspPairFlux
  exact integrable_finsetSum _ fun l _ =>
    (integrable_iteratedDeriv_mul_iteratedDeriv _ _).const_mul _

theorem integrable_thetaCuspSymFlux (n m : ℕ) : Integrable (thetaCuspSymFlux n m) := by
  unfold thetaCuspSymFlux
  split_ifs
  · exact integrable_thetaCuspPairFlux _ _
  · exact integrable_thetaCuspPairFlux _ _

/-- The flux of the pair `(i,j)` of a Hankel form: zero for odd `i+j`, and for `i+j = 2n`
`(−1)^n Σ_m C(2n,m)(−1)^{2n−m} B_m − 4^n (−1)^{n+i} B_i` with `B_m` the symmetric flux. -/
def thetaCuspHankelPairFlux (i j : ℕ) : ℝ → ℝ :=
  if Even (i+j) then fun y =>
    (-1:ℝ)^((i+j)/2) * ∑ m ∈ Finset.range (i+j+1),
      ((i+j).choose m : ℝ) * (-1:ℝ)^(i+j-m) * thetaCuspSymFlux ((i+j)/2) m y -
    2^(i+j) * (-1:ℝ)^((i+j)/2+i) * thetaCuspSymFlux ((i+j)/2) i y
  else fun _ => 0

private theorem re_neg_I_pow_mul_I_pow (i j : ℕ) :
    ((-Complex.I)^i * Complex.I^j).re = (-1:ℝ)^i * (Complex.I^(i+j)).re := by
  rw [neg_pow, mul_assoc, ← pow_add]
  rcases neg_one_pow_eq_or ℝ i with h | h <;>
    · have hc : ((-1:ℂ))^i = (((-1:ℝ)^i : ℝ) : ℂ) := by push_cast; rfl
      rw [hc, Complex.re_ofReal_mul]

private theorem re_I_pow_even (n : ℕ) : (Complex.I^(2*n)).re = (-1:ℝ)^n := by
  rw [pow_mul, Complex.I_sq]
  have : ((-1:ℂ))^n = (((-1:ℝ)^n : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.ofReal_re]

private theorem re_I_pow_odd (n : ℕ) : (Complex.I^(2*n+1)).re = 0 := by
  rw [pow_succ, pow_mul, Complex.I_sq]
  have : ((-1:ℂ))^n = (((-1:ℝ)^n : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul, Complex.I_re, mul_zero]

private theorem re_neg_I_pow (k : ℕ) : ((-Complex.I)^k).re = (-1:ℝ)^k * (Complex.I^k).re := by
  have := re_neg_I_pow_mul_I_pow k 0
  simpa using this

/-- **Pairwise square-plus-flux law.** `h_{i+j} − 4^{(i+j)/2}·Re((−i)^i i^j)·φ_i φ_j` is the
derivative of the pair flux. -/
theorem hasDerivAt_thetaCuspHankelPairFlux (i j : ℕ) (y : ℝ) :
    HasDerivAt (thetaCuspHankelPairFlux i j)
      (thetaCuspNativeSignedJet y (i+j) - 2^(i+j) * ((-Complex.I)^i * Complex.I^j).re *
        (iteratedDeriv i thetaCuspFullSource y * iteratedDeriv j thetaCuspFullSource y)) y := by
  unfold thetaCuspHankelPairFlux
  split_ifs with he
  · obtain ⟨n, hn⟩ := he
    have hij : i + j = 2*n := by omega
    have hn2 : (i+j)/2 = n := by omega
    have hji : j = 2*n - i := by omega
    rw [hn2, hij]
    have hsum := HasDerivAt.fun_sum (u := Finset.range (2*n+1)) (x := y) (fun m hm =>
      (hasDerivAt_thetaCuspSymFlux (n := n) (m := m) (by simp at hm; omega) y).const_mul
        (((2*n).choose m : ℝ) * (-1:ℝ)^(2*n-m)))
    have hi := (hasDerivAt_thetaCuspSymFlux (n := n) (m := i) (by omega) y).const_mul
      ((2:ℝ)^(2*n) * (-1:ℝ)^(n+i))
    refine ((hsum.const_mul ((-1:ℝ)^n)).sub hi).congr_deriv ?_
    have hjet : thetaCuspNativeSignedJet y (2*n) = (-1:ℝ)^n * ∑ m ∈ Finset.range (2*n+1),
        ((2*n).choose m : ℝ) * (-1:ℝ)^(2*n-m) * (iteratedDeriv m thetaCuspFullSource y *
          iteratedDeriv (2*n-m) thetaCuspFullSource y) := by
      unfold thetaCuspNativeSignedJet
      rw [re_neg_I_pow, re_I_pow_even, thetaCuspNativeReflectionJet_eq, Finset.mul_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [pow_mul, show ((-1:ℝ))^2 = 1 by norm_num, one_pow]
      ring
    have hgram : ((-Complex.I)^i * Complex.I^j).re = (-1:ℝ)^(n+i) := by
      rw [re_neg_I_pow_mul_I_pow, hij, re_I_pow_even, pow_add]
      ring
    have hchoose : ∑ m ∈ Finset.range (2*n+1), ((2*n).choose m : ℝ) = 2^(2*n) := by
      exact_mod_cast Nat.sum_range_choose (2*n)
    have hpair : ∀ m ∈ Finset.range (2*n+1), ((2*n).choose m : ℝ) * (-1:ℝ)^(2*n-m) *
        (iteratedDeriv m thetaCuspFullSource y * iteratedDeriv (2*n-m) thetaCuspFullSource y -
          (-1:ℝ)^(n+m) * (iteratedDeriv n thetaCuspFullSource y *
            iteratedDeriv n thetaCuspFullSource y)) =
        ((2*n).choose m : ℝ) * (-1:ℝ)^(2*n-m) * (iteratedDeriv m thetaCuspFullSource y *
          iteratedDeriv (2*n-m) thetaCuspFullSource y) -
          (-1:ℝ)^n * (((2*n).choose m : ℝ) * (iteratedDeriv n thetaCuspFullSource y *
            iteratedDeriv n thetaCuspFullSource y)) := by
      intro m hm
      have hm' : m ≤ 2*n := by simp at hm; omega
      have hs : (-1:ℝ)^(2*n-m) * (-1:ℝ)^(n+m) = (-1:ℝ)^n := by
        rw [← pow_add, show 2*n-m+(n+m) = n + 2*n by omega, pow_add, pow_mul]
        norm_num
      linear_combination (-(((2*n).choose m : ℝ)) * (iteratedDeriv n thetaCuspFullSource y *
        iteratedDeriv n thetaCuspFullSource y)) * hs
    have hsq : ((-1:ℝ)^n)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hsq2 : ((-1:ℝ)^(n+i))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hjet, hgram, hji, Finset.sum_congr rfl hpair, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hchoose]
    linear_combination (-(2:ℝ)^(2*n) * (iteratedDeriv n thetaCuspFullSource y *
      iteratedDeriv n thetaCuspFullSource y)) * hsq +
      ((2:ℝ)^(2*n) * (iteratedDeriv n thetaCuspFullSource y *
        iteratedDeriv n thetaCuspFullSource y)) * hsq2
  · obtain ⟨n, hn⟩ := Nat.not_even_iff_odd.mp he
    have hgram : ((-Complex.I)^i * Complex.I^j).re = 0 := by
      rw [re_neg_I_pow_mul_I_pow, hn, re_I_pow_odd, mul_zero]
    have hjet : thetaCuspNativeSignedJet y (i+j) = 0 := by
      unfold thetaCuspNativeSignedJet
      rw [re_neg_I_pow, hn, re_I_pow_odd, mul_zero, zero_mul]
    rw [hgram, hjet]
    simpa using hasDerivAt_const y (0:ℝ)

theorem integrable_thetaCuspHankelPairFlux (i j : ℕ) :
    Integrable (thetaCuspHankelPairFlux i j) := by
  unfold thetaCuspHankelPairFlux
  split_ifs
  · refine Integrable.sub (Integrable.const_mul ?_ _) ((integrable_thetaCuspSymFlux _ _).const_mul _)
    exact integrable_finsetSum _ fun m _ => (integrable_thetaCuspSymFlux _ _).const_mul _
  · exact integrable_zero _ _ _

/-- The flux of a finite section: `B_v = Σ_{i,j} v_i v_j B_{ij}`. -/
def thetaCuspNativeFlux {N : ℕ} (v : Fin N → ℝ) (y : ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i * v j * thetaCuspHankelPairFlux i j y

/-- The Gram square `|G_v(y)|² = |Σ_j v_j (2i)^j Φ^{(j)}(y)|²` expanded in real pairings. -/
theorem normSq_thetaCuspGramVector {N : ℕ} (v : Fin N → ℝ) (y : ℝ) :
    Complex.normSq (∑ j : Fin N,
      ((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource y : ℝ) : ℂ) * Complex.I^(j : ℕ)) =
    ∑ i : Fin N, ∑ j : Fin N, v i * v j * (2^((i : ℕ) + j) * ((-Complex.I)^(i : ℕ) *
      Complex.I^(j : ℕ)).re * (iteratedDeriv i thetaCuspFullSource y *
        iteratedDeriv j thetaCuspFullSource y)) := by
  have hn : ∀ z : ℂ, Complex.normSq z = ((starRingEnd ℂ) z * z).re := fun z => by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [hn, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal, map_pow, Complex.conj_I]
  have hz : ((v i * 2^(i : ℕ) * iteratedDeriv i thetaCuspFullSource y : ℝ) : ℂ) *
      (-Complex.I)^(i : ℕ) *
      (((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource y : ℝ) : ℂ) * Complex.I^(j : ℕ)) =
      (((v i * 2^(i : ℕ) * iteratedDeriv i thetaCuspFullSource y) *
        (v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource y) : ℝ) : ℂ) *
          ((-Complex.I)^(i : ℕ) * Complex.I^(j : ℕ)) := by push_cast; ring
  rw [hz, Complex.re_ofReal_mul, pow_add]
  ring

/-- **Square plus null Lagrangian.** At every center the native fibre form of every finite
section is the Gram square plus the derivative of the flux:
`Σ v_i v_j h_{i+j}(y) = |G_v(y)|² + B_v'(y)`. -/
theorem hasDerivAt_thetaCuspNativeFlux {N : ℕ} (v : Fin N → ℝ) (y : ℝ) :
    HasDerivAt (thetaCuspNativeFlux v)
      (thetaCuspNativeFibreForm (2*y) v - Complex.normSq (∑ j : Fin N,
        ((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource y : ℝ) : ℂ) * Complex.I^(j : ℕ)))
      y := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (x := y) fun (i : Fin N) _ =>
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (x := y) fun (j : Fin N) _ =>
      (hasDerivAt_thetaCuspHankelPairFlux (i : ℕ) (j : ℕ) y).const_mul (v i * v j)
  unfold thetaCuspNativeFlux
  refine h.congr_deriv ?_
  rw [normSq_thetaCuspGramVector]
  unfold thetaCuspNativeFibreForm
  rw [show 2*y/2 = y by ring, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Each tail is twice the jet integral beyond the center: `U_k(r) = 2∫_{y>r/2} h_k(y)`. -/
theorem thetaCuspNativeSignedJetTail_eq_two_mul (k : ℕ) (r : ℝ) :
    thetaCuspNativeSignedJetTail k r = 2 * ∫ y in Ioi (r/2), thetaCuspNativeSignedJet y k := by
  unfold thetaCuspNativeSignedJetTail
  have h := integral_comp_mul_left_Ioi (fun y => thetaCuspNativeSignedJet y k) r
    (b := 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1/2 : ℝ) * r = r/2 by ring] at h
  rw [show (fun s : ℝ => thetaCuspNativeSignedJet (s/2) k) =
    fun s => thetaCuspNativeSignedJet (1/2 * s) k from funext fun s => by ring_nf, h]
  norm_num

/-- **Pairwise tail law.** `U_{i+j}(r) = 2∫_{y>r/2} 4^{…}Re((−i)^i i^j) φ_i φ_j − 2B_{ij}(r/2)`. -/
theorem thetaCuspNativeSignedJetTail_eq_gram_sub_flux (i j : ℕ) (r : ℝ) :
    thetaCuspNativeSignedJetTail (i+j) r =
      2 * (∫ y in Ioi (r/2), 2^(i+j) * ((-Complex.I)^i * Complex.I^j).re *
        (iteratedDeriv i thetaCuspFullSource y * iteratedDeriv j thetaCuspFullSource y)) -
      2 * thetaCuspHankelPairFlux i j (r/2) := by
  have hgi : Integrable fun y => 2^(i+j) * ((-Complex.I)^i * Complex.I^j).re *
      (iteratedDeriv i thetaCuspFullSource y * iteratedDeriv j thetaCuspFullSource y) :=
    (integrable_iteratedDeriv_mul_iteratedDeriv i j).const_mul _
  have hderiv := hasDerivAt_thetaCuspHankelPairFlux i j
  have hd'int : Integrable fun y => thetaCuspNativeSignedJet y (i+j) -
      2^(i+j) * ((-Complex.I)^i * Complex.I^j).re *
        (iteratedDeriv i thetaCuspFullSource y * iteratedDeriv j thetaCuspFullSource y) :=
    (integrable_thetaCuspNativeSignedJet (i+j)).sub hgi
  have hlim : Tendsto (thetaCuspHankelPairFlux i j) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := r/2) (fun y _ => hderiv y)
      hd'int.integrableOn (integrable_thetaCuspHankelPairFlux i j).integrableOn
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (hderiv (r/2)).continuousAt.continuousWithinAt (fun y _ => hderiv y) hd'int.integrableOn hlim
  rw [integral_sub (integrable_thetaCuspNativeSignedJet (i+j)).integrableOn hgi.integrableOn]
    at hftc
  rw [thetaCuspNativeSignedJetTail_eq_two_mul]
  linear_combination 2 * hftc

/-- **Tail form = bulk square mass − local flux.** At every center `x = r/2` the tail form of
every finite section is `2∫_{y>x} |G_v|² − 2B_v(x)`. -/
theorem thetaCuspNativeTailHankelForm_eq_square_sub_flux {N : ℕ} (r : ℝ) (v : Fin N → ℝ) :
    thetaCuspNativeTailHankelForm r v =
      2 * (∫ y in Ioi (r/2), Complex.normSq (∑ j : Fin N,
        ((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource y : ℝ) : ℂ) * Complex.I^(j : ℕ))) -
      2 * thetaCuspNativeFlux v (r/2) := by
  have hint (i j : Fin N) : Integrable fun y => v i * v j * (2^((i : ℕ) + j) *
      ((-Complex.I)^(i : ℕ) * Complex.I^(j : ℕ)).re * (iteratedDeriv i thetaCuspFullSource y *
        iteratedDeriv j thetaCuspFullSource y)) :=
    ((integrable_iteratedDeriv_mul_iteratedDeriv i j).const_mul _).const_mul _
  simp_rw [normSq_thetaCuspGramVector]
  rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ => hint i j).integrableOn]
  unfold thetaCuspNativeTailHankelForm thetaCuspNativeFlux
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).integrableOn, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [thetaCuspNativeSignedJetTail_eq_gram_sub_flux, integral_const_mul (v i * v j)]
  ring

end
end RHTower
