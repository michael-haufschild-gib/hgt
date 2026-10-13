import GaloisForLFunctions.RHTower.DirichletFamilyPrimeMeanSquare
import GaloisForLFunctions.RHTower.Sieve.FareySet
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The multiplicative large sieve

For a primitive Dirichlet character `ψ` modulo `r` and `e = e(·/r)` the standard additive
character, the Gauss sum `τ(ψ) = ∑_b ψ(b) e(b)` satisfies `|τ(ψ)|² = r` (`normSq_gaussSum_of_isPrimitive`),
and `ψ̄(n) τ(ψ) = ∑_b ψ(b) e(nb)` for every `n`.  Hence, with `S(θ) = ∑_{n < N} c_n e(nθ)`,

`∑_{ψ primitive mod r} |∑_{n<N} c_n ψ̄(n)|² ≤ (φ(r)/r) ∑_{(a,r)=1} |S(a/r)|²`

(`sum_primitive_normSq_le`), by character orthogonality.  Summing over `r ≤ R` against the additive
large sieve at Farey fractions gives the **multiplicative large sieve**

`∑_{r ≤ R} (r/φ(r)) ∑_{ψ primitive mod r} |∑_{n<N} c_n ψ̄(n)|² ≤ (N + R²(1 + log(R²/2 + 1))) ∑ |c_n|²`

(`multiplicative_largeSieve`).
-/

open Complex ComplexConjugate

noncomputable section

namespace RHTower

variable {r : ℕ} [NeZero r]

/-- The standard additive character modulo `r`. -/
abbrev stdChar (r : ℕ) [NeZero r] : AddChar (ZMod r) ℂ := ZMod.stdAddChar

lemma norm_stdChar (x : ZMod r) : ‖stdChar r x‖ = 1 := by
  rw [stdChar, ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma conj_stdChar (x : ZMod r) : conj (stdChar r x) = stdChar r (-x) := by
  have h1 : stdChar r x * stdChar r (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn := norm_stdChar x
  have h2 : stdChar r x * conj (stdChar r x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  have hx0 : stdChar r x ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  exact mul_left_cancel₀ hx0 (h2.trans h1.symm)

/-- Additive orthogonality: `∑_a e(a(b − b')) = r [b = b']`. -/
lemma sum_stdChar_mul_sub (b b' : ZMod r) :
    ∑ a : ZMod r, stdChar r (a * (b - b')) = if b = b' then (r : ℂ) else 0 := by
  rw [AddChar.sum_mulShift (b - b') (ZMod.isPrimitive_stdAddChar r), ZMod.card]
  simp [sub_eq_zero]

lemma norm_dirichletChar_inv_apply (ψ : DirichletCharacter ℂ r) (a : ZMod r) :
    ‖ψ⁻¹ a‖ = ‖ψ a‖ := by
  rw [MulChar.inv_apply_eq_inv', norm_inv]
  by_cases ha : IsUnit a
  · have h1 : ‖ψ a‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one ψ ha.unit
      rwa [IsUnit.unit_spec] at this
    rw [h1, inv_one]
  · rw [MulChar.map_nonunit _ ha, norm_zero, inv_zero]

/-- `|∑_b f(b) e(ab)|²` summed over `a` is `r ∑_b |f(b)|²` (Parseval on `ℤ/r`). -/
lemma sum_normSq_stdChar_transform (f : ZMod r → ℂ) :
    ∑ a : ZMod r, ‖∑ b : ZMod r, f b * stdChar r (a * b)‖ ^ 2 = r * ∑ b : ZMod r, ‖f b‖ ^ 2 := by
  have hc : ∀ z : ℂ, (‖z‖ ^ 2 : ℝ) = (z * conj z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hexp : ∀ a : ZMod r, (∑ b : ZMod r, f b * stdChar r (a * b))
      * conj (∑ b : ZMod r, f b * stdChar r (a * b))
      = ∑ b : ZMod r, ∑ b' : ZMod r, f b * conj (f b') * stdChar r (a * (b - b')) := by
    intro a
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [RingHom.map_mul, conj_stdChar]
    have he : stdChar r (a * b) * stdChar r (-(a * b')) = stdChar r (a * (b - b')) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [← he]; ring
  simp_rw [hc, hexp]
  rw [← Complex.re_sum, Finset.sum_comm]
  have : ∑ b : ZMod r, ∑ a : ZMod r, ∑ b' : ZMod r, f b * conj (f b') * stdChar r (a * (b - b'))
      = ∑ b : ZMod r, ((r : ℂ) * (f b * conj (f b))) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_stdChar_mul_sub]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hn : ∀ b : ZMod r, f b * conj (f b) = ((‖f b‖ ^ 2 : ℝ) : ℂ) := fun b => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hn] at this
  rw [this]
  have : ∑ b : ZMod r, (r : ℂ) * ((‖f b‖ ^ 2 : ℝ) : ℂ) = (((r : ℝ) * ∑ b : ZMod r, ‖f b‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [Finset.mul_sum]
  rw [this, Complex.ofReal_re]
  congr 1
  exact Finset.sum_congr rfl fun b _ => hc (f b)

/-- **The Gauss sum of a primitive character has absolute value `√r`.** -/
theorem normSq_gaussSum_of_isPrimitive {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) :
    ‖gaussSum ψ (stdChar r)‖ ^ 2 = r := by
  set τ := gaussSum ψ (stdChar r) with hτ
  have hshift : ∀ a : ZMod r, ∑ b : ZMod r, ψ b * stdChar r (a * b) = ψ⁻¹ a * τ := by
    intro a
    have := gaussSum_mulShift_of_isPrimitive (stdChar r) hψ a
    rw [hτ]
    simpa [gaussSum, AddChar.mulShift_apply] using this
  have hP := sum_normSq_stdChar_transform (r := r) (fun b => ψ b)
  simp_rw [hshift, norm_mul, mul_pow, norm_dirichletChar_inv_apply] at hP
  rw [← Finset.sum_mul] at hP
  set U := ∑ a : ZMod r, ‖ψ a‖ ^ 2 with hU
  have hU1 : 1 ≤ U := by
    have h1 : ‖ψ 1‖ ^ 2 = 1 := by rw [map_one, norm_one, one_pow]
    calc (1 : ℝ) = ‖ψ 1‖ ^ 2 := h1.symm
      _ ≤ U := Finset.single_le_sum (f := fun a => ‖ψ a‖ ^ 2) (fun a _ => by positivity)
          (Finset.mem_univ 1)
  have hU0 : U ≠ 0 := by linarith
  have := mul_left_cancel₀ hU0 (hP.trans (mul_comm _ _))
  exact this

/-- `ψ̄(n) τ(ψ) = ∑_b ψ(b) e(nb)` for a primitive `ψ`. -/
lemma conj_mul_gaussSum_of_isPrimitive {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive)
    (a : ZMod r) :
    conj (ψ a) * gaussSum ψ (stdChar r) = ∑ b : ZMod r, ψ b * stdChar r (a * b) := by
  have := gaussSum_mulShift_of_isPrimitive (stdChar r) hψ a
  rw [← MulChar.star_apply', Complex.star_def] at this
  simpa [gaussSum, AddChar.mulShift_apply] using this.symm

/-- Character Parseval on `(ℤ/r)^×`: `∑_ψ |∑_b ψ(b) g(b)|² = φ(r) ∑_{b unit} |g(b)|²`. -/
lemma sum_dirichletChar_normSq (g : ZMod r → ℂ) :
    ∑ ψ : DirichletCharacter ℂ r, ‖∑ b : ZMod r, ψ b * g b‖ ^ 2
      = r.totient * ∑ b ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit, ‖g b‖ ^ 2 := by
  classical
  have hc : ∀ z : ℂ, (‖z‖ ^ 2 : ℝ) = (z * conj z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hexp : ∀ ψ : DirichletCharacter ℂ r, (∑ b : ZMod r, ψ b * g b) * conj (∑ b : ZMod r, ψ b * g b)
      = ∑ b : ZMod r, ∑ b' : ZMod r, (g b * conj (g b')) * (ψ b * conj (ψ b')) := by
    intro ψ
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [RingHom.map_mul]; ring
  simp_rw [hc, hexp]
  rw [← Complex.re_sum, Finset.sum_comm]
  have hinner : ∀ b : ZMod r, ∑ ψ : DirichletCharacter ℂ r, ∑ b' : ZMod r,
      (g b * conj (g b')) * (ψ b * conj (ψ b'))
      = if IsUnit b then (r.totient : ℂ) * (g b * conj (g b)) else 0 := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_dirichletChar_mul_conj]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_eq_single b]
    · by_cases hb : IsUnit b
      · simp [hb]; ring
      · simp [hb]
    · intro b' _ hne
      rw [if_neg]; rintro ⟨_, h⟩; exact hne h.symm
    · simp
  simp_rw [hinner]
  rw [← Finset.sum_filter, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show ((r.totient : ℂ)) = ((r.totient : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]

open Classical in
/-- **Primitive characters of one modulus.**  With `S(b) = ∑_{n<N} c_n e(nb)`,
`∑_{ψ primitive} |∑_{n<N} c_n ψ̄(n)|² ≤ (φ(r)/r) ∑_{b unit} |S(b)|²`. -/
theorem sum_primitive_normSq_le (N : ℕ) (c : ℕ → ℂ) :
    ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
        ‖∑ n ∈ Finset.range N, c n * conj (ψ n)‖ ^ 2
      ≤ (r.totient : ℝ) / r * ∑ b ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
          ‖∑ n ∈ Finset.range N, c n * stdChar r (n * b)‖ ^ 2 := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  set S : ZMod r → ℂ := fun b => ∑ n ∈ Finset.range N, c n * stdChar r (n * b) with hS
  have hprim : ∀ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
      ‖∑ n ∈ Finset.range N, c n * conj (ψ n)‖ ^ 2 = ‖∑ b : ZMod r, ψ b * S b‖ ^ 2 / r := by
    intro ψ hψ
    have hψp : ψ.IsPrimitive := (Finset.mem_filter.mp hψ).2
    have hτ := normSq_gaussSum_of_isPrimitive hψp
    have hkey : (∑ n ∈ Finset.range N, c n * conj (ψ n)) * gaussSum ψ (stdChar r)
        = ∑ b : ZMod r, ψ b * S b := by
      rw [Finset.sum_mul]
      simp_rw [mul_assoc, conj_mul_gaussSum_of_isPrimitive hψp, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [← hkey, norm_mul, mul_pow, hτ, mul_div_assoc, div_self hr0.ne', mul_one]
  rw [Finset.sum_congr rfl hprim, ← Finset.sum_div, div_le_iff₀ hr0]
  have hall : ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
      ‖∑ b : ZMod r, ψ b * S b‖ ^ 2 ≤ ∑ ψ : DirichletCharacter ℂ r, ‖∑ b : ZMod r, ψ b * S b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
  rw [sum_dirichletChar_normSq] at hall
  refine hall.trans (le_of_eq ?_)
  rw [hS]
  field_simp

/-- `e(na/q) = circleFreq(a/q)^n`. -/
lemma stdChar_natCast_mul (q : ℕ) [NeZero q] (n a : ℕ) :
    stdChar q ((n : ZMod q) * (a : ZMod q)) = (Sieve.circleFreq ((a : ℝ) / q)) ^ n := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [show ((n : ZMod q) * (a : ZMod q)) = (((n * a : ℕ) : ℤ) : ZMod q) by push_cast; ring,
    stdChar, ZMod.stdAddChar_coe, Sieve.circleFreq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The units of `ℤ/q` against the reduced residues `1 ≤ a ≤ q`. -/
lemma sum_units_eq_sum_coprime (q : ℕ) [NeZero q] (F : ZMod q → ℝ) :
    ∑ b ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, F b
      = ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q), F (a : ZMod q) := by
  classical
  have hq : 0 < q := NeZero.pos q
  refine Finset.sum_nbij' (fun b => if b.val = 0 then q else b.val) (fun a => (a : ZMod q))
    ?_ ?_ ?_ ?_ ?_
  · intro b hb
    have hbu : IsUnit b := (Finset.mem_filter.mp hb).2
    simp only [Finset.mem_filter, Finset.mem_Icc]
    split_ifs with h0
    · have hb0 : b = 0 := (ZMod.val_eq_zero b).mp h0
      have hq1 : q = 1 := by
        rw [hb0] at hbu
        by_contra hne
        haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hne
        exact not_isUnit_zero hbu
      subst hq1; simp
    · refine ⟨⟨Nat.pos_of_ne_zero h0, (ZMod.val_lt b).le⟩, ?_⟩
      have := (ZMod.isUnit_iff_coprime b.val q).mp (by rwa [ZMod.natCast_zmod_val])
      exact this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime a q).mpr ha.2⟩
  · intro b _
    split_ifs with h0
    · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero b).mp h0).symm
    · exact ZMod.natCast_zmod_val b
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    rcases lt_or_eq_of_le ha.1.2 with hlt | heq
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, if_neg (by omega)]
    · subst heq; rw [ZMod.natCast_self, ZMod.val_zero, if_pos rfl]
  · intro b _
    congr 1
    split_ifs with h0
    · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero b).mp h0)
    · exact (ZMod.natCast_zmod_val b).symm

open Classical in
/-- **The multiplicative large sieve.**  For `R ≥ 2` and coefficients `c_n`, `n < N`,
`∑_{q ≤ R} (q/φ(q)) ∑_{ψ primitive mod q} |∑_{n<N} c_n ψ̄(n)|² ≤ (N + R²(1 + log(R²/2 + 1))) ∑ |c_n|²`. -/
theorem multiplicative_largeSieve (N R : ℕ) (hR : 2 ≤ R) (c : ℕ → ℂ) :
    ∑ r ∈ Finset.range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ Finset.range N, c n * conj (ψ n)‖ ^ 2
      ≤ ((N : ℝ) + (R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2 / 2 + 1)))
          * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  set c' : Fin N → ℂ := fun n => c n with hc'
  have hterm : ∀ r ∈ Finset.range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
      ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ Finset.range N, c n * conj (ψ n)‖ ^ 2
      ≤ ∑ a ∈ (Finset.Icc 1 (r + 1)).filter (fun a => Nat.Coprime a (r + 1)),
          ‖Sieve.expSum N c' ((a : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 := by
    intro r _
    have hφ : (0 : ℝ) < (r + 1).totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos r)
    have hq : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
    have h := sum_primitive_normSq_le (r := r + 1) N c
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / (r + 1).totient)
    refine h2.trans (le_of_eq ?_)
    rw [← mul_assoc, show ((r + 1 : ℕ) : ℝ) / (r + 1).totient * ((r + 1).totient / ((r + 1 : ℕ) : ℝ)) = 1 by
      field_simp, one_mul, sum_units_eq_sum_coprime]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    rw [Sieve.expSum, Finset.sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [stdChar_natCast_mul]
  have hsum := Finset.sum_le_sum hterm
  refine hsum.trans ?_
  have hreindex : ∑ r ∈ Finset.range R, ∑ a ∈ (Finset.Icc 1 (r + 1)).filter (fun a => Nat.Coprime a (r + 1)),
        ‖Sieve.expSum N c' ((a : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2
      = ∑ q ∈ Finset.Icc 1 R, ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖Sieve.expSum N c' ((a : ℝ) / (q : ℝ))‖ ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (f := fun q =>
      ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖Sieve.expSum N c' ((a : ℝ) / (q : ℝ))‖ ^ 2) 0 R 1]
    have hI : Finset.Ico (0 + 1) (R + 1) = Finset.Icc 1 R := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hI]
  rw [hreindex]
  have hls := Sieve.largeSieve_expSum_double N hR c'
  have hcoef : ∑ n : Fin N, ‖c' n‖ ^ (2 : ℕ) = ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
    rw [Finset.sum_range]
  rw [hcoef] at hls
  exact hls

end RHTower
