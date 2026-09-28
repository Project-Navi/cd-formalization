/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Basic
import CdFormal.Axioms
import CdFormal.Theorems
import CdFormal.OperatorLemmas
import CdFormal.CoefficientLemmas
import CdFormal.ScalingUniqueness
import CdFormal.MonotoneFixedPoint
import CdFormal.LinftyAlgebraic
import CdFormal.Graph.Basic
import CdFormal.Graph.Spectral
import CdFormal.Graph.FixedPoint
import CdFormal.Graph.Existence
import CdFormal.Graph.Example
import CdFormal.Verify

/-!
# Creative Determinant formalization

The root module. It imports every module of the library, so building it builds all of them, and
CI checks that no tracked module under `CdFormal/` is missing from the list above.
-/
