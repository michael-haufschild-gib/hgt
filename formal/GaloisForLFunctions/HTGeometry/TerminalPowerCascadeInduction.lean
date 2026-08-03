import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian

/-!
# The terminal-power cascade induction

The one-step Bell reductions replace an output `H` with `δH = U H` by the next output `U` and drop
one coordinate.  Iterating them along a triangular flag of coordinates turns a chain of outputs

`Y_0, Y_1, ..., Y_m`,  `δ Y_(k+1) = Y_k · Y_(k+1)`,

into a single determinant identity: the output-jet Jacobian of `Y_m` on `m+1` coordinates is, up to
sign, the product of the terminal derivatives `P_k Y_k`, the powers `Y_k^k`, and the one-variable
base derivative `P_0 Y_0`.  Two hypotheses drive the induction and nothing else is used:

* **triangularity** — the `k`-th coordinate derivation kills every jet of every lower output;
* **nonvanishing diagonal** — the `k`-th coordinate derivation does not kill `Y_k`.

In the intended application every output is a power `Y_(k+1) = C_k X_k^(q_k)` of the coordinate that
`P_(k+1)` differentiates, so the diagonal entry is `q_k C_k X_k^(q_k - 1)`; the exponent `q_k` is the
only thing that can make it vanish.  That is the exact compression wall of the cascade: a nonzero
exponent at every level forces the whole output jet to be algebraically independent, and the size of
the exponent is irrelevant.
-/

noncomputable section

namespace GaloisForLFunctions

/-- The output-jet Jacobian of the depth-`m` output against the first `m+1` coordinate
derivations. -/
def cascadeOutputJacobian
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun i j => P (j : ℕ) (((δ : R → R)^[(i : ℕ)]) (Y m))

theorem cascadeOutputJacobian_succ
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R) (m : ℕ) :
    cascadeOutputJacobian δ P Y (m + 1)
      = derivationIterateOutputJacobian δ m (fun j : Fin (m + 2) => P (j : ℕ)) (Y (m + 1)) :=
  rfl

theorem derivationLowerJetJacobian_eq_cascadeOutputJacobian
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R) (m : ℕ) :
    derivationLowerJetJacobian δ m (fun j : Fin (m + 2) => P (j : ℕ)) (Y m)
      = cascadeOutputJacobian δ P Y m := by
  funext i j
  simp [derivationLowerJetJacobian, cascadeOutputJacobian]

/-- **The cascade determinant recursion.**  One level of the flag contributes the terminal
derivative of the output, a power of the output, and the exact cofactor sign. -/
theorem cascadeOutputJacobian_det_succ
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R) (m : ℕ)
    (hchain : δ (Y (m + 1)) = Y m * Y (m + 1))
    (htri : ∀ i : ℕ, P (m + 1) (((δ : R → R)^[i]) (Y m)) = 0) :
    (cascadeOutputJacobian δ P Y (m + 1)).det
      = (-1 : R) ^ (m + 1) * P (m + 1) (Y (m + 1)) * Y (m + 1) ^ (m + 1)
        * (cascadeOutputJacobian δ P Y m).det := by
  rw [cascadeOutputJacobian_succ,
    derivationIterateOutputJacobian_det_terminalScaled δ m (fun j : Fin (m + 2) => P (j : ℕ))
      (Y (m + 1)) (Y m) hchain (fun i => by simpa using htri (i : ℕ)),
    derivationLowerJetJacobian_eq_cascadeOutputJacobian]
  simp

/-- **The terminal-power cascade induction.**  A triangular flag of coordinate derivations with a
nonvanishing diagonal makes the full output-jet Jacobian of the terminal output nonzero at every
depth.  Every level contributes exactly one nonzero factor; no level can be compressed. -/
theorem cascadeOutputJacobian_det_ne_zero
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R)
    (hchain : ∀ k, δ (Y (k + 1)) = Y k * Y (k + 1))
    (hnz : ∀ k, Y k ≠ 0)
    (htri : ∀ k l i, l < k → P k (((δ : R → R)^[i]) (Y l)) = 0)
    (hbase : P 0 (Y 0) ≠ 0)
    (hdiag : ∀ k, P (k + 1) (Y (k + 1)) ≠ 0) :
    ∀ m, (cascadeOutputJacobian δ P Y m).det ≠ 0 := by
  intro m
  induction m with
  | zero =>
      have h : (cascadeOutputJacobian δ P Y 0).det = P 0 (Y 0) := by
        rw [Matrix.det_fin_one]
        rfl
      rw [h]
      exact hbase
  | succ m ih =>
      rw [cascadeOutputJacobian_det_succ δ P Y m (hchain m)
        (fun i => htri (m + 1) m i (by omega))]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hdiag m))
          (pow_ne_zero _ (hnz (m + 1))))
        ih

/-- **Cascade observability.**  Under the triangular flag hypotheses the first `m+2` time iterates
of the terminal output are algebraically independent over `ℂ`. -/
theorem algebraicIndependent_cascadeOutput
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R)
    (hchain : ∀ k, δ (Y (k + 1)) = Y k * Y (k + 1))
    (hnz : ∀ k, Y k ≠ 0)
    (htri : ∀ k l i, l < k → P k (((δ : R → R)^[i]) (Y l)) = 0)
    (hbase : P 0 (Y 0) ≠ 0)
    (hdiag : ∀ k, P (k + 1) (Y (k + 1)) ≠ 0) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun i : Fin (m + 2) => ((δ : R → R)^[(i : ℕ)]) (Y (m + 1))) := by
  refine algebraicIndependent_derivationIterates_of_det_ne_zero δ m
    (fun j : Fin (m + 2) => P (j : ℕ)) (Y (m + 1)) ?_
  rw [← cascadeOutputJacobian_succ]
  exact cascadeOutputJacobian_det_ne_zero δ P Y hchain hnz htri hbase hdiag (m + 1)

/-! ## The power form of the diagonal -/

/-- The terminal derivative of a pure power output. -/
theorem terminal_deriv_power
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (C X : R) (q : ℕ)
    (hC : D C = 0) (hX : D X = 1) :
    D (C * X ^ q) = (q : R) * C * X ^ (q - 1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hC, hX]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  ring

/-- In a field that is a `ℂ`-algebra a positive natural number is invertible. -/
theorem natCast_ne_zero_of_pos
    {R : Type*} [Field R] [Algebra ℂ R] {q : ℕ} (hq : 0 < q) : (q : R) ≠ 0 := by
  simpa only [map_natCast, map_zero] using
    (algebraMap ℂ R).injective.ne (Nat.cast_ne_zero.mpr hq.ne')

/-- **The exponent is the only wall.**  If every output above the base is a positive power of the
coordinate its own derivation differentiates, the diagonal of the flag never vanishes. -/
theorem cascadeOutputJacobian_det_ne_zero_of_power
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R)
    (C X : ℕ → R) (q : ℕ → ℕ)
    (hchain : ∀ k, δ (Y (k + 1)) = Y k * Y (k + 1))
    (hnz : ∀ k, Y k ≠ 0)
    (htri : ∀ k l i, l < k → P k (((δ : R → R)^[i]) (Y l)) = 0)
    (hbase : P 0 (Y 0) ≠ 0)
    (hY : ∀ k, Y (k + 1) = C k * X k ^ q k)
    (hPC : ∀ k, P (k + 1) (C k) = 0)
    (hPX : ∀ k, P (k + 1) (X k) = 1)
    (hq : ∀ k, 0 < q k) (hC : ∀ k, C k ≠ 0) (hX : ∀ k, X k ≠ 0) :
    ∀ m, (cascadeOutputJacobian δ P Y m).det ≠ 0 := by
  refine cascadeOutputJacobian_det_ne_zero δ P Y hchain hnz htri hbase fun k => ?_
  rw [hY k, terminal_deriv_power (P (k + 1)) (C k) (X k) (q k) (hPC k) (hPX k)]
  exact mul_ne_zero (mul_ne_zero (natCast_ne_zero_of_pos (hq k)) (hC k))
    (pow_ne_zero _ (hX k))

/-- **Positive-exponent cascade observability.**  Every level of a triangular power cascade costs
exactly one algebraically independent output jet, whatever the size of its exponent. -/
theorem algebraicIndependent_cascadeOutput_of_power
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R)
    (C X : ℕ → R) (q : ℕ → ℕ)
    (hchain : ∀ k, δ (Y (k + 1)) = Y k * Y (k + 1))
    (hnz : ∀ k, Y k ≠ 0)
    (htri : ∀ k l i, l < k → P k (((δ : R → R)^[i]) (Y l)) = 0)
    (hbase : P 0 (Y 0) ≠ 0)
    (hY : ∀ k, Y (k + 1) = C k * X k ^ q k)
    (hPC : ∀ k, P (k + 1) (C k) = 0)
    (hPX : ∀ k, P (k + 1) (X k) = 1)
    (hq : ∀ k, 0 < q k) (hC : ∀ k, C k ≠ 0) (hX : ∀ k, X k ≠ 0) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun i : Fin (m + 2) => ((δ : R → R)^[(i : ℕ)]) (Y (m + 1))) := by
  refine algebraicIndependent_derivationIterates_of_det_ne_zero δ m
    (fun j : Fin (m + 2) => P (j : ℕ)) (Y (m + 1)) ?_
  rw [← cascadeOutputJacobian_succ]
  exact cascadeOutputJacobian_det_ne_zero_of_power δ P Y C X q hchain hnz htri hbase hY
    hPC hPX hq hC hX (m + 1)

end GaloisForLFunctions

end
