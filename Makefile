# Seven Bridges: common tasks. Run `make help` for the list.
SHELL := /bin/bash
LAKE := $(HOME)/.elan/bin/lake

.PHONY: help build audit test check difftest wasm pack web dev preview e2e randomness server clean

help:          ## Show this list
	@grep -E '^[a-z0-9-]+:.*##' $(MAKEFILE_LIST) | awk -F':.*## ' '{printf "  make %-11s %s\n", $$1, $$2}'

build:         ## Build the Lean project (rules, proofs, #guard tests, native backend)
	$(LAKE) build

audit: build   ## Print the axioms of every main theorem
	$(LAKE) env lean Checks/Audit.lean

test: build    ## Fail on any sorry/admit/native_decide; the #guard tests run during the build
	@! grep -rnwE 'sorry|admit|native_decide' SevenBridges Main.lean Wasm.lean
	@echo "no sorry, admit or native_decide"

check:         ## lake check and lake check --paranoid in a Linux container (needs Docker)
	docker run --rm --privileged -v "$(CURDIR)":/work -v sbelan:/root/.elan ubuntu:24.04 bash /work/Checks/lakecheck.sh

difftest: build ## Fast solver vs plain solver on fresh random maps
	$(LAKE) build difftest
	cd tools && node maplines.mjs 5:101 6:102 5:103 > /tmp/sb-maps.jsonl
	.lake/build/bin/difftest < /tmp/sb-maps.jsonl

wasm:          ## Rebuild the browser engine (Lean -> WebAssembly; needs Docker)
	wasm/build.sh

pack: build    ## Remake the starter pack of proven towns
	node wasm/make-pack.mjs 20 20 20

web:           ## Static build of the game (same as the Pages deploy)
	npm ci --prefix tools
	cd web && npm ci --ignore-scripts && npx vite build --base=/sevenbridges/

dev:           ## Run the game locally (in-browser engine)
	cd web && npx vite

preview: web   ## Serve the static build
	cd web && npx vite preview

e2e:           ## Play every size in a browser against a running preview (make preview first)
	cd web && node scripts/test-wasm.mjs "http://localhost:4173/sevenbridges/?test"

randomness:    ## Check that new towns are all different (needs the bridge: make server)
	cd tools && node randomcheck.mjs 30

server: build  ## Native backend behind a WebSocket (use the game with ?server)
	cd server && npm install && node bridge.mjs

clean:         ## Remove build output
	$(LAKE) clean
	rm -rf web/dist
