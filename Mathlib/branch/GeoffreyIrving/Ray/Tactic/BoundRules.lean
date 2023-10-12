/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Std.Tactic.LabelAttr

/-!
## `bound_rules` label for use with the `bound` tactic
-/

open Lean Elab Meta

-- Rules used by the bound tactic
register_label_attr bound_rules

-- Trace class for the bound tactic
initialize registerTraceClass `bound
