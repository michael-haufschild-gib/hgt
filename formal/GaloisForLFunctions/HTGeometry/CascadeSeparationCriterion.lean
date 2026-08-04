import GaloisForLFunctions.HTGeometry.ClunieSeparationBridge
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# The cascade separation criterion in terms of the maximum term

The point selection delivers a value of the dependent state that dominates its maximum term.  Taking
the maximum term as the lower bound in the separation criterion reduces the whole Clunie argument to
one numeric inequality: the Clunie weight must be below `log μ(s)`.

That inequality is where the growth of the composition enters, and it is the only place where it
does.
-/

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- **The separation criterion in terms of the maximum term.**  If the dependent state is the entire
function with coefficients `a`, and at a selected point the top grouped coefficient has a floor, the
block is bounded, and the Clunie weight is below `log μ(s)`, then the family separates its last
state. -/
theorem separatesLast_of_maxTerm_bound {F : Fin (k + 1) → ℂ → ℂ} {a : ℕ → ℂ}
    (hlast : ∀ z : ℂ, F (Fin.last k) z = coeffFun a z)
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (s : ℝ) (z : ℂ) (c₀ W : ℝ), ‖z‖ = s ∧ 0 < c₀ ∧ 0 < maxTerm a s ∧
        c₀ ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖)) ≤ W ∧
        maxTerm a s ≤ ‖coeffFun a z‖ ∧
        W + (N : ℝ) * Real.posLog (1 / c₀)
          + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 < Real.log (maxTerm a s)) :
    SeparatesLast F := by
  refine separatesLast_of_value_bound ?_
  intro S A N hN1 hN hex
  obtain ⟨s, z, c₀, W, hznorm, hc₀, hμpos, hfloor, hW, hmax, hlt⟩ := h S A N hN1 hN hex
  refine ⟨z, W, c₀, maxTerm a s, hc₀, hμpos, hfloor, hW, ?_, hlt⟩
  rw [hlast z]
  exact hmax

/-- **Cascade independence in terms of the maximum term.** -/
theorem polyIndependent_of_maxTerm_bound {n : ℕ} (F : Fin n → ℂ → ℂ) (a : ℕ → ℕ → ℂ)
    (hlast : ∀ (m : ℕ) (hm : m + 1 ≤ n), ∀ z : ℂ,
      F (Fin.castLE hm (Fin.last m)) z = coeffFun (a m) z)
    (h : ∀ (m : ℕ) (hm : m + 1 ≤ n),
      ∀ (S : Finset (Fin (m + 1) → ℕ)) (A : (Fin (m + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
        1 ≤ N → (∀ e ∈ S, e (Fin.last m) ≤ N) →
        (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w)
          (fun i => F (Fin.castLE hm i) w) N ≠ 0) →
        ∃ (s : ℝ) (z : ℂ) (c₀ W : ℝ), ‖z‖ = s ∧ 0 < c₀ ∧ 0 < maxTerm (a m) s ∧
          c₀ ≤ ‖groupedCoeff S (fun e => (A e).eval z)
            (fun i => F (Fin.castLE hm i) z) N‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last m), (e i : ℝ)
                * Real.posLog ‖F (Fin.castLE hm i) z‖)) ≤ W ∧
          maxTerm (a m) s ≤ ‖coeffFun (a m) z‖ ∧
          W + (N : ℝ) * Real.posLog (1 / c₀)
            + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
            < Real.log (maxTerm (a m) s)) :
    PolyIndependent F :=
  polyIndependent_of_chain n F fun m hm =>
    separatesLast_of_maxTerm_bound (hlast m hm) (h m hm)

/-! ## Decomposing the floor term

The floor produced by the minimum modulus has the shape `H^n · L`, so the weight's floor term splits
into a part linear in the zero count `n` and a part depending only on the Borel--Carathéodory
constant. -/

/-- **The floor term splits.**  For `0 < H ≤ 1`,

  `log⁺(1/(H^n·L)) ≤ n·log(1/H) + log⁺(1/L)`.  No hypothesis on `L` is needed: the splitting
is an identity and `posLog` is submultiplicative unconditionally. -/
theorem posLog_inv_pow_mul_le {H L : ℝ} {n : ℕ} (hH : 0 < H) (hH1 : H ≤ 1) :
    Real.posLog (1 / (H ^ n * L)) ≤ (n : ℝ) * Real.log (1 / H) + Real.posLog (1 / L) := by
  have hHn : (0 : ℝ) < H ^ n := pow_pos hH n
  have hsplit : 1 / (H ^ n * L) = (1 / H) ^ n * (1 / L) := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  have hone : (1 : ℝ) ≤ 1 / H := by
    rw [le_div_iff₀ hH]
    linarith
  have hpow : Real.posLog ((1 / H) ^ n) = (n : ℝ) * Real.log (1 / H) := by
    have hge : (1 : ℝ) ≤ (1 / H) ^ n := one_le_pow₀ hone
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (le_trans zero_le_one hge)]; exact hge),
      Real.log_pow]
  rw [hsplit]
  refine le_trans Real.posLog_mul ?_
  rw [hpow]

/-- **The Clunie weight, decomposed.**  With the block bound `W`, the floor `H^n·L` and the relation
data, the weight is bounded by an expression linear in the zero count `n`. -/
theorem clunie_weight_le_of_floor_shape {S : Finset (Fin (k + 1) → ℕ)} {N n : ℕ}
    {W H L : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) :
    W + (N : ℝ) * Real.posLog (1 / (H ^ n * L))
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
      ≤ W + (N : ℝ) * ((n : ℝ) * Real.log (1 / H) + Real.posLog (1 / L))
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 := by
  have h := posLog_inv_pow_mul_le (H := H) (L := L) (n := n) hH hH1
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h hN
  linarith

/-! ## The grouped coefficient's own growth

The zero count of the top grouped coefficient enters the weight, and Jensen bounds it by that
coefficient's growth.  Its growth is in turn bounded by the same data as the block: the coefficient
polynomials and the earlier states. -/

/-- **The grouped coefficient's growth, from sup bounds.**  Combining the corpus's
`posLog_norm_groupedCoeff_le` with the block bound. -/
theorem posLog_norm_groupedCoeff_le_of_sup {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {j : ℕ} {α β D : ℝ}
    (hA : ∀ e ∈ S, Real.posLog ‖A e‖ ≤ α)
    (hx : ∀ i ∈ Finset.univ.erase (Fin.last k), Real.posLog ‖x i‖ ≤ β) (hβ : 0 ≤ β)
    (hD : ∀ e ∈ S, ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) ≤ D)
    (hαD : 0 ≤ α + D * β) :
    Real.posLog ‖groupedCoeff S A x j‖
      ≤ (S.card : ℝ) * (α + D * β) + (S.card : ℝ) * Real.log 2 := by
  classical
  have hbase := posLog_norm_groupedCoeff_le S A x j
  have hfiltersub : S.filter (fun e => e (Fin.last k) = j) ⊆ S := Finset.filter_subset _ _
  have hblock := clunie_block_le (S := S.filter (fun e => e (Fin.last k) = j)) (A := A) (x := x)
    (a := α) (b := β) (D := D)
    (fun e he => hA e (hfiltersub he)) hx hβ (fun e he => hD e (hfiltersub he))
  have hcard : ((S.filter (fun e => e (Fin.last k) = j)).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le S _
  have hmono : ((S.filter (fun e => e (Fin.last k) = j)).card : ℝ) * (α + D * β)
      ≤ (S.card : ℝ) * (α + D * β) := mul_le_mul_of_nonneg_right hcard hαD
  linarith

/-! ## From the growth bound to the zero count -/

/-- **A `log⁺` bound is an exponential modulus bound.** -/
theorem norm_le_exp_of_posLog_le {x : ℂ} {B : ℝ} (h : Real.posLog ‖x‖ ≤ B) :
    ‖x‖ ≤ Real.exp B := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
  · rw [← h0]
    exact le_of_lt (Real.exp_pos B)
  · have hlog : Real.log ‖x‖ ≤ B := le_trans (le_max_right _ _) h
    calc ‖x‖ = Real.exp (Real.log ‖x‖) := (Real.exp_log h0).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr hlog

/-- **The zero count, bounded by the block data.**  Jensen's count bound with the boundary maximum
replaced by the exponential of the block bound. -/
theorem count_mul_log_le_of_sup {n : ℕ} {c : ℂ} {G : ℂ → ℂ} {R R₁ MG Bd : ℝ}
    (hMG0 : 0 < MG) (hMG : MG ≤ Real.exp Bd)
    (hjensen : (n : ℝ) * Real.log (R / R₁) ≤ Real.log MG - Real.log ‖G c‖) :
    (n : ℝ) * Real.log (R / R₁) ≤ Bd - Real.log ‖G c‖ := by
  have hlog : Real.log MG ≤ Bd := by
    have h := Real.log_le_log hMG0 hMG
    rwa [Real.log_exp] at h
  linarith

/-- **The zero count itself.**  Dividing by the logarithmic range. -/
theorem count_le_of_sup {n : ℕ} {c : ℂ} {G : ℂ → ℂ} {R R₁ Bd : ℝ}
    (hpos : 0 < Real.log (R / R₁))
    (hbound : (n : ℝ) * Real.log (R / R₁) ≤ Bd - Real.log ‖G c‖) :
    (n : ℝ) ≤ (Bd - Real.log ‖G c‖) / Real.log (R / R₁) := by
  rw [le_div_iff₀ hpos]
  exact hbound

/-! ## The weight, fully explicit

Assembling the pieces: the block bound, the floor decomposition and the zero-count bound give a
bound on the Clunie weight in which every term is an explicit function of the relation data and the
earlier states' growth. -/

/-- **The Clunie weight, bounded explicitly.**  No term refers to the dependent state. -/
theorem clunie_weight_le_explicit {S : Finset (Fin (k + 1) → ℕ)} {N n : ℕ}
    {W α β D H L R R₁ Bd Gc : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1)
    (hn : (n : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁))
    (hW : W ≤ (S.card : ℝ) * (α + D * β)) :
    W + (N : ℝ) * Real.posLog (1 / (H ^ n * L))
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
      ≤ (S.card : ℝ) * (α + D * β)
        + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
            + Real.posLog (1 / L))
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 := by
  have hlogH : 0 ≤ Real.log (1 / H) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hH]
    linarith
  have hfloor := posLog_inv_pow_mul_le (H := H) (L := L) (n := n) hH hH1
  have hcount : (n : ℝ) * Real.log (1 / H)
      ≤ ((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H) :=
    mul_le_mul_of_nonneg_right hn hlogH
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hstep : (N : ℝ) * Real.posLog (1 / (H ^ n * L))
      ≤ (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
          + Real.posLog (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ hN
    linarith
  linarith

/-! ## The final criterion

Everything the Clunie argument needs, with the weight written out.  A caller supplies a selected
point together with the selection constants and the one numeric inequality; the separation follows. -/

/-- **`SeparatesLast` from the explicit inequality.**  The obligation is a single comparison between
an expression in the relation data and the earlier states' growth, and `log μ(s)` for the dependent
state. -/
theorem separatesLast_of_explicit_bound {F : Fin (k + 1) → ℂ → ℂ} {a : ℕ → ℂ}
    (hlast : ∀ z : ℂ, F (Fin.last k) z = coeffFun a z)
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (s : ℝ) (z : ℂ) (α β D H L R R₁ Bd Gc : ℝ) (n : ℕ),
        ‖z‖ = s ∧ 0 < H ∧ H ≤ 1 ∧ 0 < H ^ n * L ∧ 0 < maxTerm a s ∧
        H ^ n * L ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖))
          ≤ (S.card : ℝ) * (α + D * β) ∧
        maxTerm a s ≤ ‖coeffFun a z‖ ∧
        (n : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁) ∧
        (S.card : ℝ) * (α + D * β)
            + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
                + Real.posLog (1 / L))
            + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
          < Real.log (maxTerm a s)) :
    SeparatesLast F := by
  refine separatesLast_of_maxTerm_bound hlast ?_
  intro S A N hN1 hN hex
  obtain ⟨s, z, α, β, D, H, L, R, R₁, Bd, Gc, n, hznorm, hH, hH1, hc₀pos, hμpos, hfloor,
    hW, hmax, hn, hlt⟩ := h S A N hN1 hN hex
  refine ⟨s, z, H ^ n * L, (S.card : ℝ) * (α + D * β), hznorm, hc₀pos, hμpos, hfloor, hW,
    hmax, ?_⟩
  exact lt_of_le_of_lt
    (clunie_weight_le_explicit (S := S) (N := N) (n := n) (W := (S.card : ℝ) * (α + D * β))
      (α := α) (β := β) (D := D) (H := H) (L := L) (R := R) (R₁ := R₁) (Bd := Bd) (Gc := Gc)
      hH hH1 hn le_rfl) hlt

/-- **The final criterion against an arbitrary value bound.**  Using the circle maximum rather than
the maximum term as the lower bound for the dependent state: the composition-growth chain bounds the
circle supremum directly, so routing through `μ(s)` would give away the difference for nothing. -/
theorem separatesLast_of_explicit_value_bound {F : Fin (k + 1) → ℂ → ℂ}
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (z : ℂ) (α β D H L R R₁ Bd Gc v : ℝ) (n : ℕ),
        0 < H ∧ H ≤ 1 ∧ 0 < H ^ n * L ∧ 0 < v ∧
        H ^ n * L ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖))
          ≤ (S.card : ℝ) * (α + D * β) ∧
        v ≤ ‖F (Fin.last k) z‖ ∧
        (n : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁) ∧
        (S.card : ℝ) * (α + D * β)
            + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
                + Real.posLog (1 / L))
            + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
          < Real.log v) :
    SeparatesLast F := by
  refine separatesLast_of_value_bound ?_
  intro S A N hN1 hN hex
  obtain ⟨z, α, β, D, H, L, R, R₁, Bd, Gc, v, n, hH, hH1, hc₀pos, hvpos, hfloor, hW, hv,
    hn, hlt⟩ := h S A N hN1 hN hex
  refine ⟨z, (S.card : ℝ) * (α + D * β), H ^ n * L, v, hc₀pos, hvpos, hfloor, hW, hv, ?_⟩
  exact lt_of_le_of_lt
    (clunie_weight_le_explicit (S := S) (N := N) (n := n) (W := (S.card : ℝ) * (α + D * β))
      (α := α) (β := β) (D := D) (H := H) (L := L) (R := R) (R₁ := R₁) (Bd := Bd) (Gc := Gc)
      hH hH1 hn le_rfl) hlt

/-- **Cascade independence from the final criterion.** -/
theorem polyIndependent_of_explicit_value_bound {n : ℕ} (F : Fin n → ℂ → ℂ)
    (h : ∀ (m : ℕ) (hm : m + 1 ≤ n),
      ∀ (S : Finset (Fin (m + 1) → ℕ)) (A : (Fin (m + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
        1 ≤ N → (∀ e ∈ S, e (Fin.last m) ≤ N) →
        (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w)
          (fun i => F (Fin.castLE hm i) w) N ≠ 0) →
        ∃ (z : ℂ) (α β D H L R R₁ Bd Gc v : ℝ) (q : ℕ),
          0 < H ∧ H ≤ 1 ∧ 0 < H ^ q * L ∧ 0 < v ∧
          H ^ q * L ≤ ‖groupedCoeff S (fun e => (A e).eval z)
            (fun i => F (Fin.castLE hm i) z) N‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last m), (e i : ℝ)
                * Real.posLog ‖F (Fin.castLE hm i) z‖))
            ≤ (S.card : ℝ) * (α + D * β) ∧
          v ≤ ‖F (Fin.castLE hm (Fin.last m)) z‖ ∧
          (q : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁) ∧
          (S.card : ℝ) * (α + D * β)
              + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
                  + Real.posLog (1 / L))
              + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
            < Real.log v) :
    PolyIndependent F :=
  polyIndependent_of_chain n F fun m hm => separatesLast_of_explicit_value_bound (h m hm)

/-! ## Absorbing the shift

The composition-growth chain produces the lower bound `exp B · C - sh` with `sh = ‖a‖` the shift of
the value.  Once the exponential has doubled past the shift, the subtraction costs only `log 2`. -/

/-- **The shift costs `log 2`.**  If `2·sh ≤ exp B · C`, then `W < B + log C - log 2` suffices for
`W < log (exp B · C - sh)`. -/
theorem lt_log_sub_of_lt {W B C sh : ℝ} (hC : 0 < C)
    (hhalf : 2 * sh ≤ Real.exp B * C)
    (hlt : W < B + Real.log C - Real.log 2) :
    W < Real.log (Real.exp B * C - sh) := by
  have hexp : 0 < Real.exp B * C := by positivity
  have hhalfpos : 0 < Real.exp B * C / 2 := by linarith
  have hge : Real.exp B * C / 2 ≤ Real.exp B * C - sh := by linarith
  have hlogle : Real.log (Real.exp B * C / 2) ≤ Real.log (Real.exp B * C - sh) :=
    Real.log_le_log hhalfpos hge
  have hval : Real.log (Real.exp B * C / 2) = B + Real.log C - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hexp) (by norm_num), Real.log_mul (ne_of_gt (Real.exp_pos B))
      (ne_of_gt hC), Real.log_exp]
  rw [hval] at hlogle
  linarith

/-- **Positivity of the shifted bound.** -/
theorem exp_mul_sub_pos {B C sh : ℝ} (hC : 0 < C) (hhalf : 2 * sh ≤ Real.exp B * C) :
    0 < Real.exp B * C - sh := by
  have hexp : 0 < Real.exp B * C := by positivity
  linarith

/-! ## The criterion in terms of the growth exponent

The interface the composition-growth chain feeds directly: the dependent state's lower bound is
`exp B · C - sh`, and the obligation is a comparison of the explicit weight with `B + log C - log 2`.
-/

/-- **`SeparatesLast` from a growth exponent.**  Every quantity is explicit and the only inequality
is between the weight and the growth exponent. -/
theorem separatesLast_of_growth_exponent {F : Fin (k + 1) → ℂ → ℂ}
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (z : ℂ) (α β D H L R R₁ Bd Gc B C sh : ℝ) (n : ℕ),
        0 < H ∧ H ≤ 1 ∧ 0 < H ^ n * L ∧ 0 < C ∧
        2 * sh ≤ Real.exp B * C ∧
        H ^ n * L ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖))
          ≤ (S.card : ℝ) * (α + D * β) ∧
        Real.exp B * C - sh ≤ ‖F (Fin.last k) z‖ ∧
        (n : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁) ∧
        (S.card : ℝ) * (α + D * β)
            + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
                + Real.posLog (1 / L))
            + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
          < B + Real.log C - Real.log 2) :
    SeparatesLast F := by
  refine separatesLast_of_explicit_value_bound ?_
  intro S A N hN1 hN hex
  obtain ⟨z, α, β, D, H, L, R, R₁, Bd, Gc, B, C, sh, n, hH, hH1, hc₀pos, hC, hhalf, hfloor,
    hW, hv, hn, hlt⟩ := h S A N hN1 hN hex
  exact ⟨z, α, β, D, H, L, R, R₁, Bd, Gc, Real.exp B * C - sh, n, hH, hH1, hc₀pos,
    exp_mul_sub_pos hC hhalf, hfloor, hW, hv, hn, lt_log_sub_of_lt hC hhalf hlt⟩

/-- **Cascade independence from the growth exponent.**  The form the card's theorem invokes: at every
level of the cascade the composition growth must beat the relation's weight. -/
theorem polyIndependent_of_growth_exponent {n : ℕ} (F : Fin n → ℂ → ℂ)
    (h : ∀ (m : ℕ) (hm : m + 1 ≤ n),
      ∀ (S : Finset (Fin (m + 1) → ℕ)) (A : (Fin (m + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
        1 ≤ N → (∀ e ∈ S, e (Fin.last m) ≤ N) →
        (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w)
          (fun i => F (Fin.castLE hm i) w) N ≠ 0) →
        ∃ (z : ℂ) (α β D H L R R₁ Bd Gc B C sh : ℝ) (q : ℕ),
          0 < H ∧ H ≤ 1 ∧ 0 < H ^ q * L ∧ 0 < C ∧
          2 * sh ≤ Real.exp B * C ∧
          H ^ q * L ≤ ‖groupedCoeff S (fun e => (A e).eval z)
            (fun i => F (Fin.castLE hm i) z) N‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last m), (e i : ℝ)
                * Real.posLog ‖F (Fin.castLE hm i) z‖))
            ≤ (S.card : ℝ) * (α + D * β) ∧
          Real.exp B * C - sh ≤ ‖F (Fin.castLE hm (Fin.last m)) z‖ ∧
          (q : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁) ∧
          (S.card : ℝ) * (α + D * β)
              + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
                  + Real.posLog (1 / L))
              + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
            < B + Real.log C - Real.log 2) :
    PolyIndependent F :=
  polyIndependent_of_chain n F fun m hm => separatesLast_of_growth_exponent (h m hm)

/-- **The growth exponent is achievable.**  When the exponent is linear in the number of values with
positive slope, the comparison holds for some number of values.  Specialisation of
`exists_gt_of_linear` to the shape of the criterion. -/
theorem exists_growth_exponent {Wt C β₀ γ₀ : ℝ} (hβ₀ : 0 < β₀) :
    ∃ p : ℕ, Wt < ((p : ℝ) * β₀ - γ₀) + Real.log C - Real.log 2 := by
  obtain ⟨p, hp⟩ := exists_gt_of_linear (β := β₀) (γ := γ₀)
    (W := Wt - Real.log C + Real.log 2) hβ₀
  exact ⟨p, by linarith⟩

end GaloisForLFunctions.HTGeometry
