import GaloisForLFunctions.HTGeometry.ExponentialPolynomialVandermonde

/-!
# Multi-node exponential sums with polynomial coefficients

The one-variable separation theorem says that distinct nonzero nodes separate polynomial
coefficients.  Its multi-index form is what an orbit argument needs: the exponents of several
independent large integer parameters carry the node data of a whole tuple of dilations.

> **`expPolySumMulti_eq_zero`.**  Let `Z i : Fin r → ℂ` be tuples of nonzero nodes, pairwise
> distinct as tuples, and let each coefficient be a polynomial expression `∑_e a i e ∏_s m_s^{e_s}`
> in the integer parameters.  If
> `∑_i (∑_e a i e ∏_s m_s^{e_s}) ∏_s (Z i s)^{m_s} = 0` for every tuple `m` of positive integers,
> then every `a i e` vanishes.

The proof peels the last coordinate: for a fixed value of the first `r` parameters the identity is a
one-variable exponential sum in the last one, whose nodes are the last coordinates of the tuples.
The one-variable theorem kills each coefficient of the resulting polynomial, and each of those
coefficients is an `r`-parameter identity over the fibre of tuples sharing that last coordinate.
Tuples in one fibre are still distinct in their first `r` coordinates, so the induction applies.
-/

open Finset Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Distinct node tuples separate polynomial coefficients.** -/
theorem expPolySumMulti_eq_zero : ∀ (r : ℕ) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Z : ι → Fin r → ℂ), (∀ i s, Z i s ≠ 0) → Set.InjOn Z ↑S →
    ∀ (E : Finset (Fin r → ℕ)) (a : ι → (Fin r → ℕ) → ℂ),
      (∀ i, ∀ e ∉ E, a i e = 0) →
      (∀ m : Fin r → ℕ, (∀ s, 1 ≤ m s) →
        ∑ i ∈ S, (∑ e ∈ E, a i e * ∏ s : Fin r, ((m s : ℂ)) ^ (e s))
          * ∏ s : Fin r, Z i s ^ m s = 0) →
      ∀ i ∈ S, ∀ e, a i e = 0 := by
  intro r
  induction r with
  | zero =>
    intro ι _ S Z _ hinj E a ha h i hi e
    classical
    have hsubN : ∀ x y : Fin 0 → ℕ, x = y := fun x y => funext fun s => s.elim0
    by_cases heE : e ∈ E
    · have h0 := h (fun _ => 1) (fun s => s.elim0)
      have hone : ∀ i' : ι, (∑ e' ∈ E, a i' e' * ∏ s : Fin 0, ((1 : ℕ) : ℂ) ^ (e' s))
          * ∏ s : Fin 0, Z i' s ^ (1 : ℕ) = a i' e := by
        intro i'
        rw [Finset.prod_of_isEmpty, mul_one]
        refine Finset.sum_eq_single_of_mem e heE ?_ |>.trans ?_
        · intro b _ hb
          exact absurd (hsubN b e) hb
        · rw [Finset.prod_of_isEmpty, mul_one]
      rw [Finset.sum_congr rfl (fun i' _ => hone i')] at h0
      rw [Finset.sum_eq_single_of_mem i hi ?_] at h0
      · exact h0
      · intro b hb hbi
        exact absurd (hinj hb hi (funext fun s => s.elim0)) hbi
    · exact ha i e heE
  | succ r ih =>
    intro ι _ S Z hZ hinj E a ha h i₀ hi₀ e₀
    classical
    set L : Fin (r + 1) := Fin.last r with hLdef
    set f : ι → ℂ := fun i => Z i L with hfdef
    set Timg : Finset ℂ := S.image f with hTdef
    have hfmem : ∀ i ∈ S, f i ∈ Timg := fun i hi => Finset.mem_image_of_mem f hi
    -- the fibrewise identity obtained from the one-variable theorem
    have hfib : ∀ (m' : Fin r → ℕ), (∀ s, 1 ≤ m' s) → ∀ (c : ℕ), ∀ ζ ∈ Timg,
        ∑ i ∈ S.filter (fun i => f i = ζ), ∑ e ∈ E.filter (fun e => e L = c),
          a i e * (∏ s : Fin r, ((m' s : ℂ)) ^ (e s.castSucc))
            * ∏ s : Fin r, Z i s.castSucc ^ m' s = 0 := by
      intro m' hm' c
      set p : ℂ → Polynomial ℂ := fun ζ =>
        ∑ i ∈ S.filter (fun i => f i = ζ), ∑ e ∈ E,
          Polynomial.C (a i e * (∏ s : Fin r, ((m' s : ℂ)) ^ (e s.castSucc))
            * ∏ s : Fin r, Z i s.castSucc ^ m' s) * Polynomial.X ^ (e L) with hpdef
      have heval : ∀ (ζ : ℂ) (k : ℕ), (p ζ).eval ((k : ℕ) : ℂ)
          = ∑ i ∈ S.filter (fun i => f i = ζ), ∑ e ∈ E,
              (a i e * (∏ s : Fin r, ((m' s : ℂ)) ^ (e s.castSucc)) * ((k : ℂ)) ^ (e L))
                * ∏ s : Fin r, Z i s.castSucc ^ m' s := by
        intro ζ k
        rw [hpdef]
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => ?_
        ring
      have hvan : ∀ k : ℕ, 1 ≤ k → ∑ ζ ∈ Timg, (p ζ).eval ((k : ℕ) : ℂ) * (id ζ) ^ k = 0 := by
        intro k hk
        have hpos : ∀ s : Fin (r + 1), 1 ≤ Fin.snoc (α := fun _ => ℕ) m' k s := by
          intro s
          refine Fin.lastCases ?_ ?_ s
          · rw [Fin.snoc_last]; exact hk
          · intro s'; rw [Fin.snoc_castSucc]; exact hm' s'
        have hm := h (Fin.snoc (α := fun _ => ℕ) m' k) hpos
        have hsplit : ∀ i : ι,
            (∑ e ∈ E, a i e * ∏ s : Fin (r + 1), (((Fin.snoc (α := fun _ => ℕ) m' k s : ℕ) : ℂ)) ^ (e s))
              * ∏ s : Fin (r + 1), Z i s ^ (Fin.snoc (α := fun _ => ℕ) m' k s)
            = (∑ e ∈ E, (a i e * (∏ s : Fin r, ((m' s : ℂ)) ^ (e s.castSucc))
                  * ((k : ℂ)) ^ (e L)) * ∏ s : Fin r, Z i s.castSucc ^ m' s) * (f i) ^ k := by
          intro i
          rw [Fin.prod_univ_castSucc (f := fun s : Fin (r + 1) => Z i s ^ (Fin.snoc (α := fun _ => ℕ) m' k s))]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Fin.prod_univ_castSucc
            (f := fun s : Fin (r + 1) => (((Fin.snoc (α := fun _ => ℕ) m' k s : ℕ) : ℂ)) ^ (e s))]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          rw [hfdef, hLdef]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hsplit i)] at hm
        rw [← hm]
        rw [← Finset.sum_fiberwise_of_maps_to hfmem
          (fun i => (∑ e ∈ E, (a i e * (∏ s : Fin r, ((m' s : ℂ)) ^ (e s.castSucc))
            * ((k : ℂ)) ^ (e L)) * ∏ s : Fin r, Z i s.castSucc ^ m' s) * (f i) ^ k)]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        rw [heval, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hζ : f i = ζ := (Finset.mem_filter.mp hi).2
        rw [hζ]
        rfl
      have hz0 : ∀ ζ ∈ Timg, id ζ ≠ 0 := by
        intro ζ hζ
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hζ
        exact hZ i L
      have hpzero := expPolySum_eq_zero (fun ζ : ℂ => id ζ) Timg (fun _ _ _ _ hxy => hxy)
        hz0 p hvan
      intro ζ hζ
      have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff c) (hpzero ζ hζ)
      simp only [Polynomial.coeff_zero] at hcoeff
      rw [hpdef] at hcoeff
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow] at hcoeff
      rw [← hcoeff]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hc : e L = c
      · rw [if_pos hc, if_pos hc.symm, mul_one]
      · rw [if_neg hc, if_neg (fun hcc => hc hcc.symm), mul_zero]
    -- feed the fibrewise identity to the induction hypothesis
    have hkey : ∀ (c : ℕ) (ζ : ℂ), ζ ∈ Timg →
        ∀ i ∈ S.filter (fun i => f i = ζ), ∀ e' : Fin r → ℕ, a i (Fin.snoc e' c) = 0 := by
      intro c ζ hζ
      refine ih (S.filter (fun i => f i = ζ)) (fun i s => Z i s.castSucc)
        (fun i s => hZ i s.castSucc) ?_
        ((E.filter (fun e => e L = c)).image (fun e => fun s : Fin r => e s.castSucc))
        (fun i e' => a i (Fin.snoc e' c)) ?_ ?_
      · intro x hx y hy hxy
        have hxS := (Finset.mem_filter.mp (by exact_mod_cast hx)).1
        have hyS := (Finset.mem_filter.mp (by exact_mod_cast hy)).1
        have hxζ := (Finset.mem_filter.mp (by exact_mod_cast hx)).2
        have hyζ := (Finset.mem_filter.mp (by exact_mod_cast hy)).2
        refine hinj hxS hyS (funext fun s => ?_)
        refine Fin.lastCases ?_ ?_ s
        · rw [← hLdef]
          show f x = f y
          rw [hxζ, hyζ]
        · intro s'
          exact congrFun hxy s'
      · intro i e' he'
        refine ha i (Fin.snoc e' c) (fun hmem => he' ?_)
        refine Finset.mem_image.mpr ⟨Fin.snoc e' c, Finset.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
        · rw [hLdef, Fin.snoc_last]
        · funext s
          rw [Fin.snoc_castSucc]
      · intro m' hm'
        have hf := hfib m' hm' c ζ hζ
        rw [← hf]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        rw [Finset.sum_image ?_]
        · refine Finset.sum_congr rfl fun e he => ?_
          have heL : e L = c := (Finset.mem_filter.mp he).2
          have hsnoc : (Fin.snoc (α := fun _ => ℕ) (fun s : Fin r => e s.castSucc) c) = e := by
            funext s
            refine Fin.lastCases ?_ ?_ s
            · rw [Fin.snoc_last]
              exact heL.symm
            · intro s'
              rw [Fin.snoc_castSucc]
          rw [hsnoc]
        · intro x hx y hy hxy
          have hxL : x L = c := (Finset.mem_filter.mp hx).2
          have hyL : y L = c := (Finset.mem_filter.mp hy).2
          funext s
          refine Fin.lastCases ?_ ?_ s
          · rw [← hLdef, hxL, hyL]
          · intro s'
            exact congrFun hxy s'
    have hmemfib : i₀ ∈ S.filter (fun i => f i = f i₀) :=
      Finset.mem_filter.mpr ⟨hi₀, rfl⟩
    have hlast := hkey (e₀ L) (f i₀) (hfmem i₀ hi₀) i₀ hmemfib (fun s : Fin r => e₀ s.castSucc)
    have hfin : (Fin.snoc (α := fun _ => ℕ) (fun s : Fin r => e₀ s.castSucc) (e₀ L)) = e₀ := by
      funext s
      refine Fin.lastCases ?_ ?_ s
      · rw [Fin.snoc_last]
      · intro s'
        rw [Fin.snoc_castSucc]
    rwa [hfin] at hlast

end

end GaloisForLFunctions.HTGeometry
